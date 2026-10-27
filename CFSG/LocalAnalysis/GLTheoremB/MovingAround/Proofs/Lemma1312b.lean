module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec13g
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1311

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1312b

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barAut barOf)
open scoped Pointwise

section General

variable {G : Type} [Group G] [Finite G]

theorem card_gLBConj (g : G) (H : Subgroup G) : Nat.card (GLBConj g H) = Nat.card H := by
  unfold GLBConj
  exact Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem gLBConj_inf (g : G) (A B : Subgroup G) :
    GLBConj g (A ⊓ B) = GLBConj g A ⊓ GLBConj g B := by
  ext z
  simp [mem_gLBConj, Subgroup.mem_inf]

theorem isElemAbelian_of_le {p : ℕ} {E B : Subgroup G} (hEB : E ≤ B) (hB : IsElemAbelian p B) :
    IsElemAbelian p E :=
  isElemAbelian_of_comm_pow (fun x hx y hy => elemAbelian_comm hB (hEB hx) (hEB hy))
    (fun x hx => hB.2 x (hEB hx))

theorem exists_fixed_of_normalizes {p : ℕ} (hp : p.Prime) {E : Subgroup G} {d : G}
    (hX : IsPGroup p ↥(E ⊔ Subgroup.zpowers d)) (hdE : d ∈ Subgroup.normalizer (E : Set G))
    (hE : E ≠ ⊥) : ∃ c ∈ E, c ≠ 1 ∧ d * c = c * d := by
  set X := E ⊔ Subgroup.zpowers d with hXdef
  have hEX : E ≤ X := le_sup_left
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent ↥X := hX.isNilpotent
  have hXN : X ≤ Subgroup.normalizer (E : Set G) :=
    sup_le Subgroup.le_normalizer ((Subgroup.zpowers_le).2 hdE)
  haveI hn : (E.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hEX).2 hXN
  have hne : E.subgroupOf X ≠ ⊥ := by
    intro h0
    apply hE
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hEX hx⟩ : ↥X) ∈ E.subgroupOf X := Subgroup.mem_subgroupOf.2 hx
    rw [h0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val this
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ E.subgroupOf X ⊓ Subgroup.center ↥X, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hc (eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (hcon y hy))
  obtain ⟨hwE, hwZ⟩ := Subgroup.mem_inf.1 hw
  refine ⟨(w : G), Subgroup.mem_subgroupOf.1 hwE, fun h1 => hw1 (Subtype.ext h1), ?_⟩
  have hdX : d ∈ X := (le_sup_right : Subgroup.zpowers d ≤ X) (Subgroup.mem_zpowers d)
  have := Subgroup.mem_center_iff.1 hwZ ⟨d, hdX⟩
  exact congrArg Subtype.val this

theorem zpowers_eq_of_card_prime {p : ℕ} (hp : p.Prime) {W : Subgroup G} (hW : Nat.card W = p)
    {w : G} (hwW : w ∈ W) (hw1 : w ≠ 1) : Subgroup.zpowers w = W := by
  have hle : Subgroup.zpowers w ≤ W := (Subgroup.zpowers_le).2 hwW
  have hord : orderOf w ∣ p := by
    have := orderOf_dvd_natCard (⟨w, hwW⟩ : ↥W)
    rw [hW] at this
    simpa [Subgroup.orderOf_coe] using this
  have hord1 : orderOf w ≠ 1 := fun h => hw1 (orderOf_eq_one_iff.1 h)
  have hop : orderOf w = p := ((Nat.dvd_prime hp).1 hord).resolve_left hord1
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [Nat.card_zpowers, hop, hW]

theorem eq_of_card_prime_of_rank {p : ℕ} (hp : p.Prime) {P W₁ W₂ : Subgroup G} (hP : IsPGroup p ↥P)
    (hrk : ∀ E : Subgroup G, E ≤ P → IsElemAbelian p E → Nat.card E ≤ p)
    (h₁ : W₁ ≤ P) (h₂ : W₂ ≤ P) (hc₁ : Nat.card W₁ = p) (hc₂ : Nat.card W₂ = p) : W₁ = W₂ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : 1 < p := hp.one_lt
  have hPcard : 1 < Nat.card P := by
    have := Subgroup.card_le_card_group (G := ↥P) (⊥ : Subgroup ↥P)
    have h2 : Nat.card W₁ ≤ Nat.card P := Subgroup.card_le_of_le h₁
    omega
  haveI : Nontrivial ↥P := Finite.one_lt_card_iff_nontrivial.1 hPcard
  haveI : Group.IsNilpotent ↥P := hP.isNilpotent
  have hZne : Subgroup.center ↥P ≠ ⊥ := Group.IsNilpotent.center_ne_bot ↥P
  have hZp : IsPGroup p ↥(Subgroup.center ↥P) := hP.to_subgroup _
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hZne
    rw [pow_zero] at hk
    exact Subgroup.card_eq_one.1 hk
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p
    (by rw [hk]; exact dvd_pow_self p hk0 : p ∣ Nat.card ↥(Subgroup.center ↥P))
  set zP : ↥P := (z : ↥P) with hzP
  set zG : G := (zP : G) with hzG
  have hzord : orderOf zG = p := by
    rw [hzG, Subgroup.orderOf_coe, hzP, Subgroup.orderOf_coe]
    exact hz
  have hzp : zG ^ p = 1 := by rw [← hzord]; exact pow_orderOf_eq_one zG
  have hzcent : ∀ g ∈ P, g * zG = zG * g := by
    intro g hg
    have := Subgroup.mem_center_iff.1 z.2 ⟨g, hg⟩
    exact congrArg Subtype.val this
  have key : ∀ W : Subgroup G, W ≤ P → Nat.card W = p → W = Subgroup.zpowers zG := by
    intro W hWP hWc
    obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' p (by rw [hWc] : p ∣ Nat.card W)
    set wG : G := (w : G) with hwG
    have hword : orderOf wG = p := by rw [hwG, Subgroup.orderOf_coe]; exact hw
    have hwW : wG ∈ W := w.2
    have hw1 : wG ≠ 1 := fun h => by
      rw [h, orderOf_one] at hword
      exact hp.one_lt.ne hword
    have hwp : wG ^ p = 1 := by rw [← hword]; exact pow_orderOf_eq_one wG
    have hWgen : Subgroup.zpowers wG = W := zpowers_eq_of_card_prime hp hWc hwW hw1
    by_contra hne
    have hznot : zG ∉ Subgroup.zpowers wG := by
      intro hzmem
      have hzW : zG ∈ W := hWgen ▸ hzmem
      have hz1 : zG ≠ 1 := fun h => by
        rw [h, orderOf_one] at hzord
        exact hp.one_lt.ne hzord
      have hzcard : Nat.card (Subgroup.zpowers zG) = p := by rw [Nat.card_zpowers, hzord]
      have : Subgroup.zpowers zG = W :=
        zpowers_eq_of_card_prime hp hWc hzW hz1
      exact hne this.symm
    have hcomm : wG * zG = zG * wG := hzcent wG (hWP hwW)
    have hcard := CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.card_closure_pair_eq_sq
      (p := p) hwp hzp hcomm hw1 hznot
    have hel := CFSG.SectionRank.isElemAbelian_closure_pair hwp hzp hcomm
    have hle : Subgroup.closure ({wG, zG} : Set G) ≤ P :=
      (Subgroup.closure_le _).2 (Set.insert_subset_iff.2 ⟨hWP hwW, Set.singleton_subset_iff.2 zP.2⟩)
    have := hrk _ hle hel
    rw [hcard] at this
    nlinarith
  exact (key W₁ h₁ hc₁).trans (key W₂ h₂ hc₂).symm


theorem le_centerOf_of_normal {p : ℕ} (hp : p.Prime) {R W : Subgroup G} (hR : IsPGroup p ↥R)
    (hWR : W ≤ R) (hWc : Nat.card W = p) (hN : ∀ r ∈ R, ∀ w ∈ W, r * w * r⁻¹ ∈ W) :
    W ≤ centerOf R := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Group.IsNilpotent ↥R := hR.isNilpotent
  haveI hn : (W.subgroupOf R).Normal := by
    constructor
    intro n hn g
    exact Subgroup.mem_subgroupOf.2 (hN (g : G) g.2 (n : G) (Subgroup.mem_subgroupOf.1 hn))
  have hne : W.subgroupOf R ≠ ⊥ := by
    intro h0
    have hW1 : W = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hWR hx⟩ : ↥R) ∈ W.subgroupOf R := Subgroup.mem_subgroupOf.2 hx
      rw [h0, Subgroup.mem_bot] at this
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val this
    rw [hW1, Subgroup.card_bot] at hWc
    exact hp.one_lt.ne hWc
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ W.subgroupOf R ⊓ Subgroup.center ↥R, w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hc (eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (hcon y hy))
  obtain ⟨hwW, hwZ⟩ := Subgroup.mem_inf.1 hw
  have hwW' : (w : G) ∈ W := Subgroup.mem_subgroupOf.1 hwW
  have hw1' : (w : G) ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  have hgen : Subgroup.zpowers (w : G) = W := zpowers_eq_of_card_prime hp hWc hwW' hw1'
  intro x hx
  rw [← hgen] at hx
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have hxR : (w : G) ^ k ∈ R := R.zpow_mem w.2 k
  refine Subgroup.mem_map.2 ⟨⟨(w : G) ^ k, hxR⟩, Subgroup.mem_center_iff.2 (fun g => Subtype.ext ?_), rfl⟩
  have hcomm : Commute (g : G) (w : G) := by
    have := Subgroup.mem_center_iff.1 hwZ g
    exact congrArg Subtype.val this
  exact (hcomm.zpow_right k).eq

theorem mem_of_pPower_of_normal_preim {p : ℕ} (hp : p.Prime) {X K : Subgroup G}
    (hKX : K ≤ X) (hn : (K.subgroupOf (preimBarX p X K)).Normal) {y : G}
    (hy : y ∈ preimBarX p X K) {k : ℕ} (hyk : y ^ (p ^ k) = 1) : y ∈ K := by
  haveI : Fact p.Prime := ⟨hp⟩
  set P1 := preimBarX p X K with hP1
  have hKP : K ≤ P1 := le_preimBarX p hKX
  obtain ⟨k0, hk0, hn0⟩ := exists_mul_of_mem_preimBarX p hy
  set O := GLAPPrimeCoreOf p X with hO
  have hnP : k0⁻¹ * y ∈ P1 := P1.mul_mem (P1.inv_mem (hKP hk0)) hy
  let q : ↥P1 →* ↥P1 ⧸ K.subgroupOf P1 := QuotientGroup.mk' (K.subgroupOf P1)
  have hk0q : q ⟨k0, hKP hk0⟩ = 1 := (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_subgroupOf.2 hk0)
  have hyeq : (⟨y, hy⟩ : ↥P1) = ⟨k0, hKP hk0⟩ * ⟨k0⁻¹ * y, hnP⟩ := Subtype.ext (by simp)
  have hq1 : q ⟨y, hy⟩ = q ⟨k0⁻¹ * y, hnP⟩ := by
    rw [hyeq, map_mul, hk0q, one_mul]
  have hq2 : q ⟨y, hy⟩ ^ (p ^ k) = 1 := by
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥P1) ^ (p ^ k) = 1 := Subtype.ext (by simpa using hyk)
    rw [this, map_one]
  have hq3 : q ⟨y, hy⟩ ^ (Nat.card ↥O) = 1 := by
    rw [hq1, ← map_pow]
    have : (⟨k0⁻¹ * y, hnP⟩ : ↥P1) ^ (Nat.card ↥O) = 1 := by
      apply Subtype.ext
      have h1 : (⟨k0⁻¹ * y, hn0⟩ : ↥O) ^ (Nat.card ↥O) = 1 := pow_card_eq_one'
      have h2 := congrArg Subtype.val h1
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2
    rw [this, map_one]
  have hcop : Nat.Coprime p (Nat.card ↥O) :=
    (Nat.Prime.coprime_iff_not_dvd hp).2 (not_dvd_card_glaPPrimeCoreOf hp X)
  have hg : Nat.gcd (p ^ k) (Nat.card ↥O) = 1 := (Nat.Coprime.pow_left k hcop)
  have h4 := pow_gcd_eq_one.2 ⟨hq2, hq3⟩
  rw [hg, pow_one] at h4
  have h5 : (⟨y, hy⟩ : ↥P1) ∈ K.subgroupOf P1 := (QuotientGroup.eq_one_iff _).1 h4
  exact Subgroup.mem_subgroupOf.1 h5


theorem center_iSup_eq_one {Q : Type} [Group Q] [Finite Q] {ι : Type} [Fintype ι] (K : ι → Subgroup Q)
    (hcomm : ∀ i j, K i ≠ K j → ∀ x ∈ K i, ∀ y ∈ K j, x * y = y * x)
    (hcen : ∀ i, ∀ x ∈ K i, (∀ y ∈ K i, x * y = y * x) → x = 1) :
    ∀ z ∈ ⨆ i, K i, (∀ y ∈ ⨆ i, K i, z * y = y * z) → z = 1 := by
  classical
  have key : ∀ s : Finset ι, ∀ z ∈ (⨆ i ∈ s, K i),
      (∀ y ∈ (⨆ i ∈ s, K i), z * y = y * z) → z = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro z hz _
      simpa using hz
    | insert j s hjs ih =>
      intro z hz hzc
      rw [Finset.iSup_insert] at hz hzc
      by_cases hj : K j ≤ ⨆ i ∈ s, K i
      · rw [sup_eq_right.2 hj] at hz hzc
        exact ih z hz hzc
      · have hcom : ∀ x ∈ K j, ∀ y ∈ (⨆ i ∈ s, K i), x * y = y * x := by
          intro x hx y hy
          have hle : (⨆ i ∈ s, K i) ≤ Subgroup.centralizer ({x} : Set Q) := by
            refine iSup₂_le fun i hi => ?_
            have hne : K i ≠ K j := fun h => hj (h ▸ le_iSup₂_of_le i hi le_rfl)
            intro a ha
            rw [Subgroup.mem_centralizer_singleton_iff]
            exact hcomm i j hne a ha x hx
          exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
        obtain ⟨a, ha, w, hw, rfl⟩ := exists_mul_of_mem_sup_of_commute hcom hz
        have ha1 : a = 1 := by
          refine hcen j a ha (fun y hy => ?_)
          have h1 := hzc y (Subgroup.mem_sup_left hy)
          have h2 := hcom y hy w hw
          have h3 : a * y * w = y * a * w := by
            calc a * y * w = a * (y * w) := by group
              _ = a * (w * y) := by rw [h2]
              _ = a * w * y := by group
              _ = y * (a * w) := h1
              _ = y * a * w := by group
          exact mul_right_cancel h3
        subst ha1
        rw [one_mul] at hzc ⊢
        exact ih w hw (fun y hy => hzc y (Subgroup.mem_sup_right hy))
  have := key Finset.univ
  simpa using this

theorem card_inf_centralizer_le {Q : Type} [Group Q] [Finite Q] (K₀ : Subgroup Q) (d : Q) (n : ℕ)
    (hZ : ∀ z ∈ (⨆ i : Fin n, GLBConj (d ^ (i : ℕ)) K₀),
      (∀ y ∈ (⨆ i : Fin n, GLBConj (d ^ (i : ℕ)) K₀), z * y = y * z) → z = 1)
    (hcomm0 : ∀ i : Fin n, GLBConj (d ^ (i : ℕ)) K₀ ≠ K₀ →
      ∀ x ∈ GLBConj (d ^ (i : ℕ)) K₀, ∀ y ∈ K₀, x * y = y * x) :
    Nat.card ↥((⨆ i : Fin n, GLBConj (d ^ (i : ℕ)) K₀) ⊓ Subgroup.centralizer ({d} : Set Q)) ≤
      Nat.card ↥K₀ := by
  classical
  set V : Subgroup Q := ⨆ i : Fin n, GLBConj (d ^ (i : ℕ)) K₀ with hVdef
  set Z0 : Subgroup Q := V ⊓ Subgroup.centralizer (K₀ : Set Q) with hZ0
  set C : Subgroup Q := V ⊓ Subgroup.centralizer ({d} : Set Q) with hCdef
  have hV : V ≤ K₀ ⊔ Z0 := by
    refine iSup_le fun i => ?_
    by_cases hi : GLBConj (d ^ (i : ℕ)) K₀ = K₀
    · rw [hi]
      exact le_sup_left
    · refine le_trans ?_ le_sup_right
      intro x hx
      refine Subgroup.mem_inf.2 ⟨le_iSup (fun i : Fin n => GLBConj (d ^ (i : ℕ)) K₀) i hx, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (hcomm0 i hi x hx y hy).symm
  have hCZ : ∀ x ∈ C, x ∈ Z0 → x = 1 := by
    intro x hxC hxZ
    refine hZ x hxC.1 (fun y hy => ?_)
    have hle : V ≤ Subgroup.centralizer ({x} : Set Q) := by
      refine iSup_le fun i => ?_
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hy' : d ^ (i : ℕ) * y * (d ^ (i : ℕ))⁻¹ ∈ K₀ := mem_gLBConj.1 hy
      have hxy' : Commute x (d ^ (i : ℕ) * y * (d ^ (i : ℕ))⁻¹) :=
        (Subgroup.mem_centralizer_iff.1 hxZ.2 _ hy').symm
      have hxd : Commute x d := Subgroup.mem_centralizer_singleton_iff.1 hxC.2
      have hxc : Commute x (d ^ (i : ℕ)) := hxd.pow_right _
      have hy2 : y = (d ^ (i : ℕ))⁻¹ * (d ^ (i : ℕ) * y * (d ^ (i : ℕ))⁻¹) * d ^ (i : ℕ) := by group
      have hxy : Commute x y := by
        rw [hy2]
        exact Commute.mul_right (Commute.mul_right hxc.inv_right hxy') hxc
      exact hxy.symm.eq
    exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm
  have hdec : ∀ x : ↥C, ∃ a : ↥K₀, ∃ b ∈ Z0, (a : Q) * b = (x : Q) := by
    intro x
    have hx : (x : Q) ∈ K₀ ⊔ Z0 := hV x.2.1
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 a ha) hx
    exact ⟨⟨a, ha⟩, b, hb, hab⟩
  choose f hf using hdec
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨bx, hbx, hx⟩ := hf x
    obtain ⟨by', hby, hy⟩ := hf y
    rw [hxy] at hx
    have h1 : (x : Q)⁻¹ * (y : Q) = bx⁻¹ * by' := by rw [← hx, ← hy]; group
    have h2 : (x : Q)⁻¹ * (y : Q) ∈ Z0 := h1 ▸ Z0.mul_mem (Z0.inv_mem hbx) hby
    have h3 : (x : Q)⁻¹ * (y : Q) ∈ C := C.mul_mem (C.inv_mem x.2) y.2
    exact Subtype.ext (inv_mul_eq_one.1 (hCZ _ h3 h2))
  exact Nat.card_le_card_of_injective f hinj


end General

section Config

variable {G : Type} [Group G] [Finite G] {m p : ℕ} {B M E A D T R L0 : Subgroup G} {d : G}

theorem prime_of (h : Cex1310 G m p B M E A D T R L0 d) : p.Prime := h.standing.prime

theorem ne_two_of (h : Cex1310 G m p B M E A D T R L0 d) : p ≠ 2 := h.standing.ne_two

theorem A_le_M (h : Cex1310 G m p B M E A D T R L0 d) : A ≤ M := h.pair.1.2.1.1.1.1

theorem D_le_M (h : Cex1310 G m p B M E A D T R L0 d) : D ≤ M := h.hD.1.trans (A_le_M h)

theorem d_mem_M (h : Cex1310 G m p B M E A D T R L0 d) : d ∈ M := D_le_M h h.hd.1

theorem d_pow (h : Cex1310 G m p B M E A D T R L0 d) : d ^ p = 1 := h.hD.2.1.2 d h.hd.1

theorem B_elem (h : Cex1310 G m p B M E A D T R L0 d) : IsElemAbelian p B := h.bOne.1.1

theorem B_card (h : Cex1310 G m p B M E A D T R L0 d) : Nat.card B = p ^ m := by
  have := h.bOne.1.2.1
  rwa [h.standing.rank_eq] at this

theorem B_le_R (h : Cex1310 G m p B M E A D T R L0 d) : B ≤ R :=
  (le_sup_right : B ≤ A ⊔ B).trans h.hR.2

theorem A_le_R (h : Cex1310 G m p B M E A D T R L0 d) : A ≤ R :=
  (le_sup_left : A ≤ A ⊔ B).trans h.hR.2

theorem d_mem_R (h : Cex1310 G m p B M E A D T R L0 d) : d ∈ R := A_le_R h (h.hD.1 h.hd.1)

theorem R_pgroup (h : Cex1310 G m p B M E A D T R L0 d) : IsPGroup p ↥R := h.hR.1.2.1

theorem R_le_M (h : Cex1310 G m p B M E A D T R L0 d) : R ≤ M := h.hR.1.1

theorem B_le_M (h : Cex1310 G m p B M E A D T R L0 d) : B ≤ M := (B_le_R h).trans (R_le_M h)

theorem istar_comp_M (hp : p.Prime) {L : Subgroup G} (hL : GLAPComponent p (Istar p M D) L) :
    GLAPComponent p M L :=
  Lemma1311.glaPComponent_of_normal hp (istar_le_M p M D) (Sec13g.le_normalizer_of_istar_eq rfl) hL

theorem istar_comp_conj (hp : p.Prime) {L : Subgroup G} (hL : GLAPComponent p (Istar p M D) L)
    {g : G} (hg : g ∈ M) : GLAPComponent p (Istar p M D) (GLBConj g L) := by
  have := glaPComponent_gLBConj hL g
  rwa [istar_conj_eq p hg] at this

theorem block_data (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) :
    IsGLBlock M L ∧ B ≤ Subgroup.normalizer (L : Set G) ∧ B = (B ⊓ L) ⊔ centBar p B L ∧
      (B ⊓ L) ⊓ centBar p B L = ⊥ ∧ CFSG.Open.pRank p (B ⊓ L) = CFSG.Open.pRank p L := by
  obtain ⟨⟨hbl, -, -⟩, hBN, hdec, hint, hrk⟩ := ((h133 h.toSec13).2 L hL)
  exact ⟨hbl, hBN, hdec, hint, hrk⟩

theorem card_eq_pow_of_elemAbelian {p : ℕ} (hp : p.Prime) {E : Subgroup G} (hE : IsElemAbelian p E) :
    ∃ k : ℕ, Nat.card E = p ^ k := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hPg : IsPGroup p ↥E := fun g => ⟨1, Subtype.ext (by simpa using hE.2 g g.2)⟩
  exact hPg.exists_card_eq

theorem elemAbelian_card_le {p : ℕ} (hp : p.Prime) {P L : Subgroup G} (hPL : P ≤ L)
    (hL : CFSG.Open.pRank p L = 1) :
    ∀ E : Subgroup G, E ≤ P → IsElemAbelian p E → Nat.card E ≤ p := by
  intro E hEP hE
  obtain ⟨k, hk⟩ := card_eq_pow_of_elemAbelian hp hE
  have h1 : k ≤ CFSG.Open.pRank p L := CFSG.SectionRank.le_pRank hp.one_lt (hEP.trans hPL) hE hk
  rw [hL] at h1
  rw [hk]
  calc p ^ k ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos h1
    _ = p := pow_one p

theorem pRank_alt5 : CFSG.Open.pRank 3 (⊤ : Subgroup (alternatingGroup (Fin 5))) = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    have h2 := two_mul_nat_card_alternatingGroup (α := Fin 5)
    have h3 : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
      rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
      decide
    omega
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le Nat.prime_three.one_lt (k := 1) (fun E _ hE => ?_)
    obtain ⟨k, hk⟩ := card_eq_pow_of_elemAbelian Nat.prime_three hE
    have hdvd : Nat.card E ∣ Nat.card (alternatingGroup (Fin 5)) := Subgroup.card_subgroup_dvd_card E
    rw [hk, hcard] at hdvd
    by_contra hlt
    have hk2 : 2 ≤ k := by
      by_contra hk1
      have : k ≤ 1 := by omega
      exact hlt (by rw [hk]; exact Nat.pow_le_pow_right (by norm_num) this)
    have h9 : 9 ∣ 3 ^ k := by
      have : 3 ^ 2 ∣ 3 ^ k := pow_dvd_pow 3 hk2
      simpa using this
    have := h9.trans hdvd
    omega
  · obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := alternatingGroup (Fin 5)) 3
      (by rw [hcard]; norm_num)
    have hg3 : g ^ 3 = 1 := by rw [← hg]; exact pow_orderOf_eq_one g
    have hg1 : g ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hg
      omega
    have hE : IsElemAbelian 3 (Subgroup.zpowers g) := by
      refine ⟨inferInstance, fun y hy => ?_⟩
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hg3, one_zpow]
    have hc : Nat.card (Subgroup.zpowers g) = 3 ^ 1 := by
      rw [pow_one, Nat.card_zpowers, hg]
    exact CFSG.SectionRank.le_pRank Nat.prime_three.one_lt le_top hE hc

theorem pRank_top_barOf (p : ℕ) [Fact p.Prime] (L : Subgroup G) :
    CFSG.Open.pRank p (⊤ : Subgroup (barOf p L)) = CFSG.Open.pRank p L := by
  have hN : ¬ p ∣ Nat.card (GLAPPrimeCore p ↥L) := not_dvd_card_pPrimeCore (Fact.out) L
  have h1 := CFSG.SectionRank.pRank_quotient_eq (GLAPPrimeCore p ↥L) hN
  exact h1.trans (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := p) L).symm

theorem pRank_eq_one (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) : CFSG.Open.pRank p L = 1 := by
  have hp : p.Prime := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  rcases h.h139 with ⟨hp3, hIoS, L1, hL1, hIL1, hr1, htyp⟩ | ⟨hp3, hall⟩
  · have hIL : Istar p M D = L1 := hIoS.symm.trans hIL1
    have hL1' : GLAPComponent p (Istar p M D) L1 := hIoS ▸ hL1
    rw [Lemma1311.pComp_eq_of_single hp hIL hL1' hL]
    exact hr1
  · obtain ⟨e⟩ := hall L hL
    have h1 := pRank_top_barOf p L
    have h2 := CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e
    rw [← h1, h2]
    subst hp3
    exact pRank_alt5

theorem card_B_inf (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) : Nat.card ↥(B ⊓ L) = p := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, -, -, -, hrk⟩ := block_data h133 h hL
  have hr1 : CFSG.Open.pRank p L = 1 := pRank_eq_one h hL
  have hel : IsElemAbelian p (B ⊓ L) := isElemAbelian_of_le inf_le_left (B_elem h)
  obtain ⟨k, hk⟩ := card_eq_pow_of_elemAbelian hp hel
  have hk1 : k ≤ CFSG.Open.pRank p (B ⊓ L) := CFSG.SectionRank.le_pRank hp.one_lt le_rfl hel hk
  rw [hrk, hr1] at hk1
  obtain ⟨E', hE'le, hE', hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (B ⊓ L)
  rw [hrk, hr1, pow_one] at hcard
  have hp1 := hp.one_lt
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    have := Subgroup.card_le_of_le hE'le
    omega
  have hk2 : k = 1 := by omega
  subst hk2
  simpa using hk

theorem barX_centerless (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} (hLM : GLAPComponent p M L)
    (hbl : IsGLBlock M L) :
    ∀ x ∈ barX p M L, (∀ y ∈ barX p M L, x * y = y * x) → x = 1 := by
  intro x hx hcomm
  let e := quotEquivBarX hp hLM.1 hLM.2.1
  have hZ := center_quotient_eq_bot_of_block hp hp2 hLM hbl
  have hz : e.symm ⟨x, hx⟩ ∈ Subgroup.center (↥L ⧸ GLAPPrimeCore p ↥L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact Subtype.ext (hcomm _ (e g).2).symm
  rw [hZ, Subgroup.mem_bot] at hz
  have : (⟨x, hx⟩ : ↥(barX p M L)) = 1 := by
    have h2 : e (e.symm ⟨x, hx⟩) = e 1 := by rw [hz]
    simpa using h2
  exact congrArg Subtype.val this

theorem barX_simple (hp : p.Prime) (hp2 : p ≠ 2) {L : Subgroup G} (hLM : GLAPComponent p M L)
    (hbl : IsGLBlock M L) : IsSimpleGroup ↥(barX p M L) :=
  let e1 : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* (↥L ⧸ GLAPPrimeCore p ↥L) :=
    QuotientGroup.quotientMulEquivOfEq (glaPPrimeCore_eq_pCore_two_of_block hp hp2 hLM hbl).symm
  (e1.trans (quotEquivBarX hp hLM.1 hLM.2.1)).isSimpleGroup_congr.1 hbl.simple

theorem comm_of_comp {Q : Type} [Group Q] [Finite Q] {K K' : Subgroup Q} (hK : IsComponentOf K ⊤)
    (hK' : IsComponentOf K' ⊤) (hne : K ≠ K') : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := by
  have := Sec13e.commute_of_isComponentOf hK hK' hne
  intro x hx y hy
  have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.1 this) hx
  exact (Subgroup.mem_centralizer_iff.1 h1 y hy).symm

theorem commute_of_not_le {Q : Type} [Group Q] {K V : Subgroup Q} (hK : IsSimpleGroup ↥K)
    (hKV : K ≤ Subgroup.normalizer (V : Set Q)) (hVK : V ≤ Subgroup.normalizer (K : Set Q))
    (hnot : ¬ K ≤ V) : ∀ k ∈ K, ∀ v ∈ V, k * v = v * k := by
  haveI hn : (V.subgroupOf K).Normal := by
    constructor
    intro n hn g
    exact Subgroup.mem_subgroupOf.2
      ((Subgroup.mem_normalizer_iff.1 (hKV g.2) (n : Q)).1 (Subgroup.mem_subgroupOf.1 hn))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (V.subgroupOf K) with h0 | h0
  · intro k hk v hv
    have hcomm : k * v * k⁻¹ * v⁻¹ ∈ V ⊓ K := by
      refine ⟨?_, ?_⟩
      · exact V.mul_mem ((Subgroup.mem_normalizer_iff.1 (hKV hk) v).1 hv) (V.inv_mem hv)
      · have h1 : v * k⁻¹ * v⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.1 (hVK hv) k⁻¹).1 (K.inv_mem hk)
        have e : k * v * k⁻¹ * v⁻¹ = k * (v * k⁻¹ * v⁻¹) := by group
        rw [e]
        exact K.mul_mem hk h1
    have h2 : (⟨k * v * k⁻¹ * v⁻¹, hcomm.2⟩ : ↥K) ∈ V.subgroupOf K := Subgroup.mem_subgroupOf.2 hcomm.1
    rw [h0, Subgroup.mem_bot] at h2
    have h3 : k * v * k⁻¹ * v⁻¹ = 1 := congrArg Subtype.val h2
    exact (commutatorElement_eq_one_iff_mul_comm.1 (by simpa [commutatorElement_def] using h3))
  · exfalso
    apply hnot
    intro x hx
    have : (⟨x, hx⟩ : ↥K) ∈ V.subgroupOf K := by rw [h0]; exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.1 this

theorem conj_B_inf (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) {g : G} (hg : g ∈ R) :
    GLBConj g (B ⊓ L) = B ⊓ GLBConj g L := by
  have hp := prime_of h
  have hgM : g ∈ M := R_le_M h hg
  have hL' := istar_comp_conj hp hL hgM
  have hW1 : GLBConj g (B ⊓ L) ≤ R ⊓ GLBConj g L := by
    intro x hx
    rw [gLBConj_inf] at hx
    refine ⟨?_, hx.2⟩
    have h0 : g * x * g⁻¹ ∈ B := mem_gLBConj.1 hx.1
    have h1 : g⁻¹ * (g * x * g⁻¹) * g ∈ R :=
      R.mul_mem (R.mul_mem (R.inv_mem hg) (B_le_R h h0)) hg
    simpa [mul_assoc] using h1
  have hW2 : B ⊓ GLBConj g L ≤ R ⊓ GLBConj g L :=
    le_inf (inf_le_left.trans (B_le_R h)) inf_le_right
  exact eq_of_card_prime_of_rank hp ((R_pgroup h).to_le inf_le_left)
    (elemAbelian_card_le hp (inf_le_right) (pRank_eq_one h hL')) hW1 hW2
    (by rw [card_gLBConj]; exact card_B_inf h133 h hL) (card_B_inf h133 h hL')


theorem L0_le (h : Cex1310 G m p B M E A D T R L0 d) : L0 ≤ Istar p M D ⊓ Cg d :=
  h.hL0.1.trans (Sec13g.piLayer_le_self p _)

theorem L0_le_istar (h : Cex1310 G m p B M E A D T R L0 d) : L0 ≤ Istar p M D :=
  (L0_le h).trans inf_le_left

theorem L0_comp_H (h : Cex1310 G m p B M E A D T R L0 d) :
    GLAPComponent p (Istar p M D ⊓ Cg d) L0 := by
  obtain ⟨S, hS, -, hEq⟩ := Lemma1311.pComp_piLayer_summand (prime_of h) h.hL0
  rw [hEq]
  exact hS

theorem H_le_M (h : Cex1310 G m p B M E A D T R L0 d) : Istar p M D ⊓ Cg d ≤ M :=
  inf_le_left.trans (istar_le_M p M D)

theorem d_mem_normalizer_L0 (h : Cex1310 G m p B M E A D T R L0 d) :
    d ∈ Subgroup.normalizer (L0 : Set G) := by
  refine Subgroup.centralizer_le_normalizer (L0 : Set G) ?_
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact Subgroup.mem_centralizer_singleton_iff.1 ((L0_le h) hx).2

theorem d_mem_normalizer_istar (h : Cex1310 G m p B M E A D T R L0 d) :
    d ∈ Subgroup.normalizer ((Istar p M D : Subgroup G) : Set G) :=
  mem_normalizer_iff_gLBConj_eq.2 (istar_conj_eq p (d_mem_M h))

theorem L1_conj_eq {g : G} (hg : g ∈ Istar p M D) :
    GLBConj g (L1of p M D L0) = L1of p M D L0 := by
  have h1 : ∀ {g : G}, g ∈ Istar p M D → GLBConj g (L1of p M D L0) ≤ L1of p M D L0 :=
    fun hg => conj_iSup_mem_le (M := Istar p M D) (I := L0) hg
  refine le_antisymm (h1 hg) ?_
  have h2 := gLBConj_mono g (h1 ((Istar p M D).inv_mem hg))
  rw [gLBConj_gLBConj_inv] at h2
  exact h2

theorem L1_le_istar (h : Cex1310 G m p B M E A D T R L0 d) : L1of p M D L0 ≤ Istar p M D := by
  refine iSup₂_le fun g hg => ?_
  calc GLBConj g L0 ≤ GLBConj g (Istar p M D) := gLBConj_mono g (L0_le_istar h)
    _ = Istar p M D := istar_conj_eq p (istar_le_M p M D hg)

theorem istar_le_normalizer_L1 :
    Istar p M D ≤ Subgroup.normalizer ((L1of p M D L0 : Subgroup G) : Set G) :=
  fun _ hg => mem_normalizer_iff_gLBConj_eq.2 (L1_conj_eq hg)

theorem L1_isSubnormal (h : Cex1310 G m p B M E A D T R L0 d) :
    IsSubnormal (L1of p M D L0) M := by
  have hn : ((L1of p M D L0).subgroupOf (Istar p M D)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (L1_le_istar h)).2 istar_le_normalizer_L1
  exact isSubnormal_trans' (IsSubnormal.step (L1_le_istar h) hn (IsSubnormal.refl _))
    (istar_isSubnormal p M D)

theorem conj_L1_eq {c : G} (hcI : c ∈ Subgroup.normalizer ((Istar p M D : Subgroup G) : Set G))
    (hcL : c ∈ Subgroup.normalizer ((L0 : Subgroup G) : Set G)) :
    GLBConj c (L1of p M D L0) = L1of p M D L0 := by
  have key : ∀ {c : G}, c ∈ Subgroup.normalizer ((Istar p M D : Subgroup G) : Set G) →
      c ∈ Subgroup.normalizer ((L0 : Subgroup G) : Set G) →
      GLBConj c (L1of p M D L0) ≤ L1of p M D L0 := by
    intro c hcI hcL
    unfold L1of
    rw [gLBConj_iSup_eq]
    refine iSup_le fun g => ?_
    rw [gLBConj_iSup_eq]
    refine iSup_le fun hg => ?_
    rw [gLBConj_gLBConj]
    have hg' : c⁻¹ * g * c ∈ Istar p M D := by
      have := (Subgroup.mem_normalizer_iff.1
        ((Subgroup.normalizer ((Istar p M D : Subgroup G) : Set G)).inv_mem hcI) g).1 hg
      simpa using this
    have e : g * c = c * (c⁻¹ * g * c) := by group
    rw [e, ← gLBConj_gLBConj, gLBConj_eq_of_mem_normalizer hcL]
    exact le_iSup₂_of_le (c⁻¹ * g * c) hg' le_rfl
  refine le_antisymm (key hcI hcL) ?_
  have h2 := gLBConj_mono c (key ((Subgroup.normalizer ((Istar p M D : Subgroup G) : Set G)).inv_mem hcI)
    ((Subgroup.normalizer ((L0 : Subgroup G) : Set G)).inv_mem hcL))
  rw [gLBConj_gLBConj_inv] at h2
  exact h2


noncomputable abbrev dBar (h : Cex1310 G m p B M E A D T R L0 d) : ↥M ⧸ GLAPPrimeCore p ↥M :=
  QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨d, d_mem_M h⟩

theorem barX_conj_pow (h : Cex1310 G m p B M E A D T R L0 d) (L : Subgroup G) (i : ℕ) :
    barX p M (GLBConj (d ^ i) L) = GLBConj ((dBar h) ^ i) (barX p M L) := by
  rw [barX_gLBConj_eq p (M.pow_mem (d_mem_M h) i) L]
  congr 1

theorem mem_preimBarX_of_mul {X K : Subgroup G} {j y : G} (hjK : j ∈ K) (hjX : j ∈ X) (hyX : y ∈ X)
    (hn : j⁻¹ * y ∈ GLAPPrimeCoreOf p X) : y ∈ preimBarX p X K := by
  obtain ⟨z, hz, hzeq⟩ := hn
  refine ⟨⟨y, hyX⟩, ?_, rfl⟩
  have e1 : (⟨j, hjX⟩ : ↥X)⁻¹ * ⟨y, hyX⟩ = z := Subtype.ext (by simpa using hzeq.symm)
  have e2 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨j, hjX⟩ := by
    symm
    refine (QuotientGroup.eq).2 ?_
    rw [e1]
    exact hz
  show QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨y, hyX⟩ ∈ barX p X K
  rw [e2]
  exact ⟨⟨j, hjX⟩, Subgroup.mem_subgroupOf.2 hjK, rfl⟩

theorem V1_center (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L)
    (hV : barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L)) :
    ∀ z ∈ barX p M (L1of p M D L0),
      (∀ y ∈ barX p M (L1of p M D L0), z * y = y * z) → z = 1 := by
  have hp := prime_of h
  have hp2 := ne_two_of h
  have hdM := d_mem_M h
  rw [hV]
  refine center_iSup_eq_one (fun i : Fin p => barX p M (GLBConj (d ^ (i : ℕ)) L)) ?_ ?_
  · intro i j hij x hx y hy
    exact comm_of_comp
      (Lemma1311.isComponent_barX_of_pComp hp (istar_comp_conj hp hL (M.pow_mem hdM i)))
      (Lemma1311.isComponent_barX_of_pComp hp (istar_comp_conj hp hL (M.pow_mem hdM j))) hij x hx y hy
  · intro i x hx hc
    have hLi := istar_comp_conj hp hL (M.pow_mem hdM i)
    obtain ⟨hbl, -⟩ := block_data h133 h hLi
    exact barX_centerless hp hp2 (istar_comp_M hp hLi) hbl x hx hc

theorem card_barX_le_L0 (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) :
    Nat.card ↥(barX p M L) ≤ Nat.card ↥(barX p M L0) := by
  have hp := prime_of h
  obtain ⟨e⟩ := h.hL0iso L hL
  have hLM := istar_comp_M hp hL
  have h1 : Nat.card (barOf p L0) = Nat.card (barOf p L) := Nat.card_congr e.toEquiv
  have h2 : Nat.card ↥(barX p M L) = Nat.card (barOf p L) :=
    Nat.card_congr (Lemma1311.barXIso hp hLM.1 hLM.2.1).toEquiv
  have h3 : Nat.card (barOf p L0) = Nat.card (barOf p (barX p M L0)) :=
    Nat.card_congr (Lemma1311.barOfIsoBarX hp ((L0_le h).trans (H_le_M h))).toEquiv
  have h4 : Nat.card (barOf p (barX p M L0)) ≤ Nat.card ↥(barX p M L0) :=
    Nat.card_le_card_of_surjective (QuotientGroup.mk (s := GLAPPrimeCore p ↥(barX p M L0)))
      QuotientGroup.mk_surjective
  omega

theorem d_mem_normalizer_L1 (h : Cex1310 G m p B M E A D T R L0 d) :
    d ∈ Subgroup.normalizer ((L1of p M D L0 : Subgroup G) : Set G) :=
  mem_normalizer_iff_gLBConj_eq.2
    (conj_L1_eq (d_mem_normalizer_istar h) (d_mem_normalizer_L0 h))

theorem d_isPGroup (h : Cex1310 G m p B M E A D T R L0 d) : IsPGroup p (Subgroup.zpowers d) :=
  CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.isPGroup_zpowers_of_pow_eq_one' (d_pow h)


theorem barX_L0_eq (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L)
    (hV : barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L)) :
    barX p M L0 = barX p M (L1of p M D L0) ⊓
      Subgroup.centralizer ({dBar h} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have hp := prime_of h
  have hdM := d_mem_M h
  have hL1M : L1of p M D L0 ≤ M := (L1_le_istar h).trans (istar_le_M p M D)
  have hbi := barX_inf_centralizer hp hdM hL1M (d_mem_normalizer_L1 h) (d_isPGroup h)
  have hle : barX p M L0 ≤ barX p M (L1of p M D L0) ⊓
      Subgroup.centralizer ({dBar h} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    rw [← hbi]
    exact Lemma1311.barX_mono' p (le_inf Sec13g.le_L1of (fun x hx => (L0_le h hx).2))
  have hV' : barX p M (L1of p M D L0) = ⨆ i : Fin p, GLBConj ((dBar h) ^ (i : ℕ)) (barX p M L) := by
    rw [hV]
    exact iSup_congr fun i => barX_conj_pow h L i
  have hcard := card_inf_centralizer_le (barX p M L) (dBar h) p
    (by rw [← hV']; exact V1_center h133 h hL hV)
    (by
      intro i hi x hx y hy
      rw [← barX_conj_pow h L i] at hi hx
      exact comm_of_comp
        (Lemma1311.isComponent_barX_of_pComp hp (istar_comp_conj hp hL (M.pow_mem hdM i)))
        (Lemma1311.isComponent_barX_of_pComp hp hL) hi x hx y hy)
  rw [← hV'] at hcard
  exact Subgroup.eq_of_le_of_card_ge hle (hcard.trans (card_barX_le_L0 h hL))

theorem pElem_mem_L0 (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d)
    {L : Subgroup G} (hL : GLAPComponent p (Istar p M D) L)
    (hV : barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L))
    {y : G} (hy : y ∈ L1of p M D L0 ⊓ Cg d) {k : ℕ} (hyk : y ^ (p ^ k) = 1) : y ∈ L0 := by
  have hp := prime_of h
  have hHM := H_le_M h
  have hyH : y ∈ Istar p M D ⊓ Cg d := ⟨L1_le_istar h hy.1, hy.2⟩
  have hyM : y ∈ M := hHM hyH
  have hL1M : L1of p M D L0 ≤ M := (L1_le_istar h).trans (istar_le_M p M D)
  have heq := barX_L0_eq h133 h hL hV
  have hle : barX p M (L1of p M D L0 ⊓ Cg d) ≤ barX p M L0 := by
    rw [barX_inf_centralizer hp (d_mem_M h) hL1M (d_mem_normalizer_L1 h) (d_isPGroup h)]
    exact heq.ge
  obtain ⟨j, hj, hjy⟩ := exists_of_barX_le hle hy hyM
  have hjH : j ∈ Istar p M D ⊓ Cg d := L0_le h hj
  have hn : j⁻¹ * y ∈ GLAPPrimeCoreOf p (Istar p M D ⊓ Cg d) :=
    inf_glaPPrimeCoreOf_le hp hHM ⟨(Istar p M D ⊓ Cg d).mul_mem ((Istar p M D ⊓ Cg d).inv_mem hjH) hyH, hjy⟩
  have hpre : y ∈ preimBarX p (Istar p M D ⊓ Cg d) L0 := mem_preimBarX_of_mul hj hjH hyH hn
  exact mem_of_pPower_of_normal_preim hp (L0_comp_H h).1 (glaPComponent_normal_preimBarX (L0_comp_H h))
    hpre hyk

theorem comm_bar_of_mem_core {X : Subgroup G} {b x : G} (hbX : b ∈ X) (hxX : x ∈ X)
    (h : (b * x * b⁻¹)⁻¹ * x ∈ GLAPPrimeCoreOf p X) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨b, hbX⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hxX⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hxX⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨b, hbX⟩ := by
  obtain ⟨z, hz, hzeq⟩ := h
  have hzeq' : z = ((⟨b, hbX⟩ : ↥X) * ⟨x, hxX⟩ * (⟨b, hbX⟩ : ↥X)⁻¹)⁻¹ * ⟨x, hxX⟩ :=
    Subtype.ext (by simpa using hzeq)
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X) z = 1 := (QuotientGroup.eq_one_iff z).2 hz
  rw [hzeq', map_mul, map_inv, map_mul, map_mul, map_inv] at h1
  have h2 := inv_mul_eq_one.1 h1
  exact mul_inv_eq_iff_eq_mul.1 h2

theorem comm_mod_of_mem_centBar (hp : p.Prime) {M X L : Subgroup G} (hLM : IsSubnormal L M) {c : G}
    (hc : c ∈ centBar p X L) :
    c ∈ Subgroup.normalizer (L : Set G) ∧ ∀ x ∈ L, (c * x * c⁻¹)⁻¹ * x ∈ GLAPPrimeCoreOf p M := by
  obtain ⟨hcN, hbar⟩ := mem_centK_iff.1 (Subgroup.mem_inf.1 hc).1
  refine ⟨hcN, fun x hx => ?_⟩
  have h2 : barAut p L ⟨c, hcN⟩ (QuotientGroup.mk ⟨x, hx⟩) = QuotientGroup.mk ⟨x, hx⟩ := by
    rw [hbar]
    rfl
  rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk] at h2
  have h3 := (QuotientGroup.eq).1 h2
  have h4 : (c * x * c⁻¹)⁻¹ * x ∈ GLAPPrimeCoreOf p L := ⟨_, h3, rfl⟩
  exact glaPPrimeCoreOf_le_of_isSubnormal hp hLM h4


theorem hint_holds (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d)
    {L : Subgroup G} (hL : GLAPComponent p (Istar p M D) L)
    (hV : barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L)) :
    (B ⊓ L1of p M D L0) ⊓ centBar p B (L1of p M D L0) = ⊥ := by
  have hp := prime_of h
  rw [eq_bot_iff]
  intro b hb
  obtain ⟨hbBL, hbC⟩ := Subgroup.mem_inf.1 hb
  obtain ⟨hbB, hbL1⟩ := Subgroup.mem_inf.1 hbBL
  rw [Subgroup.mem_bot]
  obtain ⟨-, hcomm⟩ := comm_mod_of_mem_centBar hp (L1_isSubnormal h) hbC
  have hbM : b ∈ M := B_le_M h hbB
  have hz : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨b, hbM⟩ = 1 := by
    refine V1_center h133 h hL hV _ ⟨⟨b, hbM⟩, Subgroup.mem_subgroupOf.2 hbL1, rfl⟩ ?_
    intro y hy
    obtain ⟨x, hx, rfl⟩ := (Lemma1311.mem_barX' p).1 hy
    exact comm_bar_of_mem_core hbM x.2 (hcomm x hx)
  have hcore : b ∈ GLAPPrimeCoreOf p M := ⟨⟨b, hbM⟩, (QuotientGroup.eq_one_iff _).1 hz, rfl⟩
  have hbot : B ⊓ GLAPPrimeCoreOf p M = ⊥ :=
    isPGroup_inf_eq_bot_of_not_dvd hp ((R_pgroup h).to_le (B_le_R h)) (not_dvd_card_glaPPrimeCoreOf hp M)
  have : b ∈ B ⊓ GLAPPrimeCoreOf p M := ⟨hbB, hcore⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact this


abbrev joinB (p : ℕ) (B M D : Subgroup G) (P : Subgroup G → Prop) : Subgroup G :=
  ⨆ (L' : Subgroup G) (_ : GLAPComponent p (Istar p M D) L' ∧ P L'), B ⊓ L'

theorem joinB_le_B (P : Subgroup G → Prop) : joinB p B M D P ≤ B :=
  iSup₂_le fun _ _ => inf_le_left

theorem d_normalizes_joinB (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d)
    (P : Subgroup G → Prop)
    (hcl : ∀ L', GLAPComponent p (Istar p M D) L' → P L' → P (GLBConj d L')) :
    d ∈ Subgroup.normalizer ((joinB p B M D P : Subgroup G) : Set G) := by
  have hp := prime_of h
  have hle : GLBConj d (joinB p B M D P) ≤ joinB p B M D P := by
    unfold joinB
    rw [gLBConj_iSup_eq]
    refine iSup_le fun L' => ?_
    rw [gLBConj_iSup_eq]
    refine iSup_le fun hL' => ?_
    rw [conj_B_inf h133 h hL'.1 (d_mem_R h)]
    exact le_iSup₂_of_le (f := fun (L' : Subgroup G) (_ : GLAPComponent p (Istar p M D) L' ∧ P L') => B ⊓ L')
      (GLBConj d L') ⟨istar_comp_conj hp hL'.1 (d_mem_M h), hcl L' hL'.1 hL'.2⟩ le_rfl
  refine mem_normalizer_iff_gLBConj_eq.2 (Subgroup.eq_of_le_of_card_ge hle ?_)
  rw [card_gLBConj]

theorem exists_fixed_point (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d)
    (P : Subgroup G → Prop)
    (hcl : ∀ L', GLAPComponent p (Istar p M D) L' → P L' → P (GLBConj d L'))
    (hne : ∃ L', GLAPComponent p (Istar p M D) L' ∧ P L') :
    ∃ c ∈ joinB p B M D P, c ≠ 1 ∧ d * c = c * d := by
  have hp := prime_of h
  obtain ⟨L', hL', hP⟩ := hne
  have hE : joinB p B M D P ≠ ⊥ := by
    intro h0
    have hle : B ⊓ L' ≤ joinB p B M D P :=
      le_iSup₂_of_le (f := fun (L' : Subgroup G) (_ : GLAPComponent p (Istar p M D) L' ∧ P L') => B ⊓ L')
        L' ⟨hL', hP⟩ le_rfl
    have hc := card_B_inf h133 h hL'
    rw [h0, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hc
    exact hp.one_lt.ne hc
  have hX : IsPGroup p ↥(joinB p B M D P ⊔ Subgroup.zpowers d) :=
    (R_pgroup h).to_le (sup_le ((joinB_le_B P).trans (B_le_R h))
      ((Subgroup.zpowers_le).2 (d_mem_R h)))
  exact exists_fixed_of_normalizes hp hX (d_normalizes_joinB h133 h P hcl) hE

theorem joinB_le_KGof (P : Subgroup G → Prop) {V : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)}
    (hV : ∀ L', GLAPComponent p (Istar p M D) L' → P L' → barX p M L' ≤ V) :
    joinB p B M D P ≤ Istar p M D ⊓ Lemma1311.KGof p M V := by
  refine iSup₂_le fun L' hL' x hx => ?_
  have hxL : x ∈ L' := (Subgroup.mem_inf.1 hx).2
  have hxI : x ∈ Istar p M D := hL'.1.1 hxL
  have hxM : x ∈ M := istar_le_M p M D hxI
  refine ⟨hxI, (Lemma1311.mem_KGof p).2 ⟨hxM, hV L' hL'.1 hL'.2 ?_⟩⟩
  exact (Lemma1311.mem_barX' p).2 ⟨⟨x, hxM⟩, hxL, rfl⟩

theorem mem_L1_of_bar (h : Cex1310 G m p B M E A D T R L0 d) {y : G} (hyI : y ∈ Istar p M D)
    (hyM : y ∈ M)
    (hyb : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨y, hyM⟩ ∈ barX p M (L1of p M D L0))
    {k : ℕ} (hyk : y ^ (p ^ k) = 1) : y ∈ L1of p M D L0 := by
  have hp := prime_of h
  obtain ⟨x, hx, hxy⟩ := (Lemma1311.mem_barX' p).1 hyb
  have hxI : (x : G) ∈ Istar p M D := L1_le_istar h hx
  have h1 : (x : G)⁻¹ * y ∈ GLAPPrimeCoreOf p M := by
    have := (QuotientGroup.eq).1 hxy
    exact ⟨_, this, by simp⟩
  have h2 : (x : G)⁻¹ * y ∈ GLAPPrimeCoreOf p (Istar p M D) := by
    rw [← glaPPrimeCoreOf_inf_eq_of_isSubnormal hp (istar_isSubnormal p M D)]
    exact ⟨(Istar p M D).mul_mem ((Istar p M D).inv_mem hxI) hyI, h1⟩
  have hpre : y ∈ preimBarX p (Istar p M D) (L1of p M D L0) :=
    mem_preimBarX_of_mul hx hxI hyI h2
  have hnorm : ((L1of p M D L0).subgroupOf (preimBarX p (Istar p M D) (L1of p M D L0))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX p (L1_le_istar h))).2
      ((preimBarX_le p _ _).trans istar_le_normalizer_L1)
  exact mem_of_pPower_of_normal_preim hp (L1_le_istar h) hnorm hpre hyk


theorem orbit_closed (h : Cex1310 G m p B M E A D T R L0 d) (L : Subgroup G) :
    ∀ L' : Subgroup G, (∃ i : Fin p, L' = GLBConj (d ^ (i : ℕ)) L) →
      ∃ i : Fin p, GLBConj d L' = GLBConj (d ^ (i : ℕ)) L := by
  have hp := prime_of h
  rintro L' ⟨i, rfl⟩
  rw [gLBConj_gLBConj, ← pow_succ]
  by_cases hi : (i : ℕ) + 1 < p
  · exact ⟨⟨(i : ℕ) + 1, hi⟩, rfl⟩
  · have hip : (i : ℕ) + 1 = p := by have := i.2; omega
    refine ⟨⟨0, hp.pos⟩, ?_⟩
    rw [hip, d_pow h]
    simp [gLBConj_one]

theorem hx_holds (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d)
    {L : Subgroup G} (hL : GLAPComponent p (Istar p M D) L)
    (hV : barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L)) :
    ∃ x ∈ B ⊓ L0, x ≠ 1 ∧ (Prop139a p M D → x ∈ centerOf R) := by
  have hp := prime_of h
  have hdM := d_mem_M h
  set P : Subgroup G → Prop := fun L' => ∃ i : Fin p, L' = GLBConj (d ^ (i : ℕ)) L with hP
  have hcl : ∀ L', GLAPComponent p (Istar p M D) L' → P L' → P (GLBConj d L') :=
    fun L' _ hL' => orbit_closed h L L' hL'
  have hne : ∃ L', GLAPComponent p (Istar p M D) L' ∧ P L' :=
    ⟨L, hL, ⟨0, hp.pos⟩, by simp [gLBConj_one]⟩
  obtain ⟨c, hcE, hc1, hcd⟩ := exists_fixed_point h133 h P hcl hne
  have hcB : c ∈ B := joinB_le_B P hcE
  have hV1 : ∀ L', GLAPComponent p (Istar p M D) L' → P L' → barX p M L' ≤ barX p M (L1of p M D L0) := by
    rintro L' - ⟨i, rfl⟩
    rw [hV]
    exact le_iSup (fun i : Fin p => barX p M (GLBConj (d ^ (i : ℕ)) L)) i
  have hcS := joinB_le_KGof P hV1 hcE
  obtain ⟨hcI, hcK⟩ := hcS
  obtain ⟨hcM, hcb⟩ := (Lemma1311.mem_KGof p).1 hcK
  have hcpow : c ^ (p ^ 1) = 1 := by rw [pow_one]; exact (B_elem h).2 c hcB
  have hcL1 : c ∈ L1of p M D L0 := mem_L1_of_bar h hcI hcM hcb hcpow
  have hcCg : c ∈ Cg d := Subgroup.mem_centralizer_singleton_iff.2 hcd.symm
  have hcL0 : c ∈ L0 := pElem_mem_L0 h133 h hL hV ⟨hcL1, hcCg⟩ hcpow
  refine ⟨c, ⟨hcB, hcL0⟩, hc1, fun ha => ?_⟩
  obtain ⟨hp3, hIoS, L1', hL1', hIL1', hr1, htyp⟩ := ha
  have hIst : GLAPComponent p (Istar p M D) (Istar p M D) := by
    have hIL : Istar p M D = L1' := hIoS.symm.trans hIL1'
    have hL1'' : GLAPComponent p (Istar p M D) L1' := hIoS ▸ hL1'
    rwa [← hIL] at hL1''
  have hWc : Nat.card ↥(B ⊓ Istar p M D) = p := card_B_inf h133 h hIst
  have hWR : B ⊓ Istar p M D ≤ R := inf_le_left.trans (B_le_R h)
  have hN : ∀ r ∈ R, ∀ w ∈ B ⊓ Istar p M D, r * w * r⁻¹ ∈ B ⊓ Istar p M D := by
    intro r hr w hw
    have h1 := conj_B_inf h133 h hIst hr
    rw [istar_conj_eq p (R_le_M h hr)] at h1
    have : w ∈ GLBConj r (B ⊓ Istar p M D) := by rw [h1]; exact hw
    exact mem_gLBConj.1 this
  exact le_centerOf_of_normal hp (R_pgroup h) hWR hWc hN ⟨hcB, L0_le_istar h hcL0⟩


theorem comm_of_mem_centerOf {R : Subgroup G} {c : G} (hc : c ∈ centerOf R) :
    c ∈ R ∧ ∀ g ∈ R, g * c = c * g := by
  obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hc
  refine ⟨y.2, fun g hg => ?_⟩
  have := Subgroup.mem_center_iff.1 hy ⟨g, hg⟩
  exact congrArg Subtype.val this

theorem mem_B_of_central (h : Cex1310 G m p B M E A D T R L0 d) {c : G} (hcR : c ∈ R)
    (hccent : ∀ g ∈ R, g * c = c * g) (hcp : c ^ p = 1) : c ∈ B := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hS : GLStanding G m p := h.standing
  have hBel : IsElemAbelian p B := B_elem h
  have hBR : B ≤ R := B_le_R h
  have hcB : ∀ b ∈ B, b * c = c * b := fun b hb => hccent b (hBR hb)
  have hcomm_zc : ∀ g ∈ Subgroup.zpowers c, ∀ b ∈ B, g * b = b * g := by
    intro g hg b hb
    obtain ⟨a, ha⟩ := Subgroup.mem_zpowers_iff.1 hg
    rw [← ha]
    exact Commute.zpow_left (hcB b hb).symm a
  have hEwN : Subgroup.zpowers c ≤ Subgroup.normalizer (B : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      have e : g * b * g⁻¹ = b := by rw [hcomm_zc g hg b hb, mul_inv_cancel_right]
      rw [e]
      exact hb
    · intro hx
      have hgx : g⁻¹ * (g * b * g⁻¹) = (g * b * g⁻¹) * g⁻¹ :=
        hcomm_zc g⁻¹ (Subgroup.inv_mem _ hg) _ hx
      have e2 : g * b * g⁻¹ * g⁻¹ * g = g * b * g⁻¹ := by group
      have hb' : g⁻¹ * (g * b * g⁻¹) * g ∈ B := by
        rw [hgx, e2]
        exact hx
      have key : g⁻¹ * (g * b * g⁻¹) * g = b := by group
      rwa [key] at hb'
  obtain ⟨Ew, hEwdef⟩ : ∃ E : Subgroup G, E = B ⊔ Subgroup.zpowers c := ⟨_, rfl⟩
  have hEwprod : (Ew : Set G) = (B : Set G) * (Subgroup.zpowers c : Set G) := by
    rw [hEwdef]
    exact Subgroup.coe_mul_of_right_le_normalizer_left B (Subgroup.zpowers c) hEwN
  have hEwcomm : ∀ x ∈ Ew, ∀ y ∈ Ew, x * y = y * x := by
    intro x hx y hy
    have hx' : x ∈ (B : Set G) * (Subgroup.zpowers c : Set G) := hEwprod ▸ hx
    have hy' : y ∈ (B : Set G) * (Subgroup.zpowers c : Set G) := hEwprod ▸ hy
    obtain ⟨b, hb, u, hu, rfl⟩ := hx'
    obtain ⟨b', hb', u', hu', rfl⟩ := hy'
    have hcb : Commute b b' := elemAbelian_comm hBel hb hb'
    have hub' : Commute u b' := hcomm_zc u hu b' hb'
    have hbu' : Commute b u' := (hcomm_zc u' hu' b hb).symm
    have huu' : Commute u u' := by
      obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
      obtain ⟨a', rfl⟩ := Subgroup.mem_zpowers_iff.1 hu'
      exact Commute.zpow_zpow_self c a a'
    have hcomm' : Commute (b * u) (b' * u') :=
      Commute.mul_right (Commute.mul_left hcb hub') (Commute.mul_left hbu' huu')
    exact hcomm'.eq
  have hEwpow : ∀ x ∈ Ew, x ^ p = 1 := by
    intro x hx
    have hx' : x ∈ (B : Set G) * (Subgroup.zpowers c : Set G) := hEwprod ▸ hx
    obtain ⟨b, hb, u, hu, rfl⟩ := hx'
    have hbu : Commute b u := (hcomm_zc u hu b hb).symm
    rw [hbu.mul_pow p, hBel.2 b hb, one_mul]
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hu
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcp, one_zpow]
  have hEel : IsElemAbelian p Ew := isElemAbelian_of_comm_pow hEwcomm hEwpow
  have hsc := lemma23_proved G m p hS B h.bOne
  have hEqB : Ew = B := hsc.2.2 Ew le_top hEel (by rw [hEwdef]; exact le_sup_left)
  have hcEw : c ∈ Ew := by
    rw [hEwdef]
    exact (le_sup_right : Subgroup.zpowers c ≤ B ⊔ Subgroup.zpowers c) (Subgroup.mem_zpowers c)
  rw [hEqB] at hcEw
  exact hcEw

theorem exists_central_order_p {p : ℕ} (hp : p.Prime) {M R N : Subgroup G} (hRM : IsSylowIn p M R)
    (hNM : N ≤ M) (hNn : ∀ g ∈ M, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hpN : p ∣ Nat.card ↥N) :
    ∃ c ∈ N ⊓ centerOf R, orderOf c = p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hRp : IsPGroup p ↥R := hRM.2.1
  have hRM' : R ≤ M := hRM.1
  have hRC : R ⊓ N ≠ ⊥ := Sec13g.inf_ne_bot_of_sylow_normal hRM hNM hNn hpN
  haveI : Group.IsNilpotent ↥R := hRp.isNilpotent
  have hHn : ((R ⊓ N).subgroupOf R).Normal := by
    constructor
    intro n hn g
    have hn' : (n : G) ∈ R ⊓ N := Subgroup.mem_subgroupOf.1 hn
    obtain ⟨hnR, hnC⟩ := Subgroup.mem_inf.1 hn'
    refine Subgroup.mem_subgroupOf.2 (Subgroup.mem_inf.2 ⟨?_, ?_⟩)
    · exact R.mul_mem (R.mul_mem g.2 hnR) (R.inv_mem g.2)
    · exact hNn (g : G) (hRM' g.2) (n : G) hnC
  have hHne : (R ⊓ N).subgroupOf R ≠ ⊥ := by
    intro h0
    apply hRC
    rw [eq_bot_iff]
    intro y hy
    have hyH : (⟨y, (Subgroup.mem_inf.1 hy).1⟩ : ↥R) ∈ (R ⊓ N).subgroupOf R :=
      Subgroup.mem_subgroupOf.2 hy
    rw [h0, Subgroup.mem_bot] at hyH
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val hyH
  obtain ⟨w, hwH, hw1⟩ : ∃ w ∈ ((R ⊓ N).subgroupOf R ⊓ Subgroup.center ↥R), w ≠ 1 := by
    by_contra hc
    push Not at hc
    exact Group.IsNilpotent.inf_center_ne_bot_of_normal hHne
      (eq_bot_iff.2 fun y hy => Subgroup.mem_bot.2 (hc y hy))
  obtain ⟨hwH', hwZ⟩ := Subgroup.mem_inf.1 hwH
  have hwN : (w : G) ∈ N := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hwH')).2
  have hwcenter : (w : G) ∈ centerOf R := Subgroup.mem_map.2 ⟨w, hwZ, rfl⟩
  have hw1' : (w : G) ≠ 1 := fun h1 => hw1 (Subtype.ext h1)
  set Z : Subgroup G := N ⊓ centerOf R with hZdef
  have hZR : Z ≤ R := inf_le_right.trans (Subgroup.map_subtype_le _)
  have hZp : IsPGroup p ↥Z := hRp.to_le hZR
  obtain ⟨k, hk⟩ := hZp.exists_card_eq
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    have hZ1 : Z = ⊥ := Subgroup.card_eq_one.1 hk
    have : (w : G) ∈ Z := ⟨hwN, hwcenter⟩
    rw [hZ1, Subgroup.mem_bot] at this
    exact hw1' this
  obtain ⟨c0, hc0⟩ := exists_prime_orderOf_dvd_card' p
    (by rw [hk]; exact dvd_pow_self p hk0 : p ∣ Nat.card ↥Z)
  refine ⟨(c0 : G), c0.2, ?_⟩
  rw [Subgroup.orderOf_coe]
  exact hc0

abbrev CN (p : ℕ) (M D L0 : Subgroup G) : Subgroup G :=
  Lemma1311.KGof p M (Subgroup.centralizer
    ((barX p M (Sec13g.L2of p M D L0) : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)))

theorem CN_le_M : CN p M D L0 ≤ M := fun _ hn => ((Lemma1311.mem_KGof p).1 hn).1

theorem L2_le_istar (h : Cex1310 G m p B M E A D T R L0 d) : Sec13g.L2of p M D L0 ≤ Istar p M D := by
  refine iSup₂_le fun g hg => ?_
  calc GLBConj g (L1of p M D L0) ≤ GLBConj g (Istar p M D) := gLBConj_mono g (L1_le_istar h)
    _ = Istar p M D := istar_conj_eq p hg

theorem M_le_normalizer_L2 :
    M ≤ Subgroup.normalizer ((Sec13g.L2of p M D L0 : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact Sec13g.normal_L2of g hg x hx
  · intro hx
    have := Sec13g.normal_L2of g⁻¹ (M.inv_mem hg) _ hx
    simpa [mul_assoc] using this

theorem CN_normal {g n : G} (hg : g ∈ M) (hn : n ∈ CN p M D L0) : g * n * g⁻¹ ∈ CN p M D L0 := by
  obtain ⟨hnM, hnc⟩ := (Lemma1311.mem_KGof p).1 hn
  have hgnM : g * n * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hg hnM) (M.inv_mem hg)
  refine (Lemma1311.mem_KGof p).2 ⟨hgnM, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  set gb : ↥M ⧸ GLAPPrimeCore p ↥M := QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hg⟩ with hgb
  have hgV : GLBConj gb (barX p M (Sec13g.L2of p M D L0)) = barX p M (Sec13g.L2of p M D L0) := by
    rw [← barX_gLBConj_eq p hg, gLBConj_eq_of_mem_normalizer (M_le_normalizer_L2 hg)]
  have hv' : gb⁻¹ * v * gb ∈ barX p M (Sec13g.L2of p M D L0) := by
    have : gb⁻¹ * v * gb ∈ GLBConj gb (barX p M (Sec13g.L2of p M D L0)) := by
      rw [mem_gLBConj]
      have e : gb * (gb⁻¹ * v * gb) * gb⁻¹ = v := by group
      rw [e]
      exact hv
    rwa [hgV] at this
  have h1 := Subgroup.mem_centralizer_iff.1 hnc _ hv'
  have e : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g * n * g⁻¹, hgnM⟩ =
      gb * QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨n, hnM⟩ * gb⁻¹ := by
    simp only [hgb, ← map_inv, ← map_mul]
    rfl
  rw [e]
  calc v * (gb * QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨n, hnM⟩ * gb⁻¹)
      = gb * ((gb⁻¹ * v * gb) * QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨n, hnM⟩) * gb⁻¹ := by group
    _ = gb * (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨n, hnM⟩ * (gb⁻¹ * v * gb)) * gb⁻¹ := by rw [h1]
    _ = (gb * QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨n, hnM⟩ * gb⁻¹) * v := by group


theorem mem_core_of_comm_bar {X : Subgroup G} {b x : G} (hbX : b ∈ X) (hxX : x ∈ X)
    (h : QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨b, hbX⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hxX⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨x, hxX⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥X) ⟨b, hbX⟩) :
    (b * x * b⁻¹)⁻¹ * x ∈ GLAPPrimeCoreOf p X := by
  have hz : ((⟨b, hbX⟩ : ↥X) * ⟨x, hxX⟩ * (⟨b, hbX⟩ : ↥X)⁻¹)⁻¹ * ⟨x, hxX⟩ ∈ GLAPPrimeCore p ↥X := by
    have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥X)
        (((⟨b, hbX⟩ : ↥X) * ⟨x, hxX⟩ * (⟨b, hbX⟩ : ↥X)⁻¹)⁻¹ * ⟨x, hxX⟩) = 1 := by
      simp only [map_mul, map_inv]
      rw [h]
      simp
    exact (QuotientGroup.eq_one_iff _).1 h1
  exact ⟨_, hz, by simp⟩

theorem mem_centBar_of_comm_mod (hp : p.Prime) {M X L : Subgroup G} (hLM : IsSubnormal L M) {c : G}
    (hcN : c ∈ Subgroup.normalizer (L : Set G)) (hcX : c ∈ X)
    (h : ∀ x ∈ L, (c * x * c⁻¹)⁻¹ * x ∈ GLAPPrimeCoreOf p M) : c ∈ centBar p X L := by
  have hbar : barAut p L ⟨c, hcN⟩ = 1 := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H x =>
      rw [CFSG.HardMathSupport.Solomon.LocalBalance.barAut_mk, MulAut.one_apply]
      refine (QuotientGroup.eq).2 ?_
      have hcx : c * (x : G) * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hcN (x : G)).1 x.2
      have h1 : (c * (x : G) * c⁻¹)⁻¹ * (x : G) ∈ L ⊓ GLAPPrimeCoreOf p M :=
        ⟨L.mul_mem (L.inv_mem hcx) x.2, h x x.2⟩
      rw [glaPPrimeCoreOf_inf_eq_of_isSubnormal hp hLM] at h1
      obtain ⟨z, hz, hzeq⟩ := h1
      have : z = (L.normalizerMonoidHom ⟨c, hcN⟩ x)⁻¹ * x := Subtype.ext hzeq
      rw [← this]
      exact hz
  exact Subgroup.mem_inf.2 ⟨Subgroup.mem_map.2 ⟨⟨c, hcN⟩, MonoidHom.mem_ker.2 hbar, rfl⟩, hcX⟩

theorem relIndex_le_of_dec {B S C T : Subgroup G}
    (hBel : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hdec : B = S ⊔ C) (hSB : S ≤ B) (hCB : C ≤ B)
    (hCT : C ≤ T) : T.relIndex B ≤ Nat.card S := by
  unfold Subgroup.relIndex
  rw [Subgroup.index_eq_card]
  refine Nat.card_le_card_of_surjective
    (fun s : ↥S => (QuotientGroup.mk ⟨s, hSB s.2⟩ : ↥B ⧸ T.subgroupOf B)) ?_
  intro q
  induction q using QuotientGroup.induction_on with
  | H b =>
    have hbSC : (b : G) ∈ S ⊔ C := by rw [← hdec]; exact b.2
    obtain ⟨s, hs, c, hc, hsc⟩ := exists_mul_of_mem_sup_of_commute (s := S) (t := C)
      (fun x hx y hy => hBel x (hSB hx) y (hCB hy)) hbSC
    refine ⟨⟨s, hs⟩, ?_⟩
    show (QuotientGroup.mk ⟨s, hSB hs⟩ : ↥B ⧸ T.subgroupOf B) = QuotientGroup.mk b
    rw [QuotientGroup.eq]
    have : (⟨s, hSB hs⟩ : ↥B)⁻¹ * b = ⟨c, hCB hc⟩ := Subtype.ext (by simp [← hsc])
    rw [this]
    exact Subgroup.mem_subgroupOf.2 (hCT hc)

theorem caseA' (h : Cex1310 G m p B M E A D T R L0 d) (hN : ¬ CN p M D L0 ≤ GLAPPrimeCoreOf p M) :
    ∃ c ∈ centBar p B (L1of p M D L0) ⊓ Cg d, c ≠ 1 ∧ c ∈ centerOf R := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hpN : p ∣ Nat.card ↥(CN p M D L0) := by
    by_contra hpC
    apply hN
    have hnorm : ((CN p M D L0).subgroupOf M).Normal := by
      constructor
      intro n hn g
      exact Subgroup.mem_subgroupOf.2 (CN_normal g.2 (Subgroup.mem_subgroupOf.1 hn))
    have hcop : Nat.Coprime p (Nat.card ↥((CN p M D L0).subgroupOf M)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe CN_le_M).toEquiv]
      exact (Nat.Prime.coprime_iff_not_dvd hp).2 hpC
    have hle := le_pPrimeCore_of_normal_coprime hnorm hcop
    intro x hx
    exact Subgroup.mem_map.2 ⟨⟨x, CN_le_M hx⟩, hle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  obtain ⟨c, hcNZ, hcord⟩ := exists_central_order_p hp h.hR.1 CN_le_M
    (fun g hg n hn => CN_normal hg hn) hpN
  obtain ⟨hcN, hcZ⟩ := Subgroup.mem_inf.1 hcNZ
  obtain ⟨hcR, hccent⟩ := comm_of_mem_centerOf hcZ
  have hcp : c ^ p = 1 := by rw [← hcord]; exact pow_orderOf_eq_one c
  have hc1 : c ≠ 1 := fun h1 => by
    rw [h1, orderOf_one] at hcord
    exact hp.one_lt.ne hcord
  have hcB : c ∈ B := mem_B_of_central h hcR hccent hcp
  have hcM : c ∈ M := R_le_M h hcR
  have hdc : d * c = c * d := hccent d (d_mem_R h)
  have hcI : c ∈ Subgroup.normalizer ((Istar p M D : Subgroup G) : Set G) :=
    mem_normalizer_iff_gLBConj_eq.2 (istar_conj_eq p hcM)
  have hcCg : c ∈ Subgroup.normalizer ((Cg d : Subgroup G) : Set G) :=
    Subgroup.mem_normalizer_iff.2 (fun x => Lemma1311.normalizes_centralizer_singleton hdc x)
  have hcH : c ∈ Subgroup.normalizer ((Istar p M D ⊓ Cg d : Subgroup G) : Set G) :=
    mem_normalizer_inf hcI hcCg
  obtain ⟨hcM', hcc⟩ := (Lemma1311.mem_KGof p).1 hcN
  have hL0L2 : barX p M L0 ≤ barX p M (Sec13g.L2of p M D L0) :=
    Lemma1311.barX_mono' p (Sec13g.le_L1of.trans Sec13g.L1_le_L2)
  have hcnorm : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨c, hcM'⟩ ∈
      Subgroup.normalizer ((barX p M L0 : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
        Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    exact Subgroup.mem_centralizer_iff.1 hcc v (hL0L2 hv)
  have hcL0 : c ∈ Subgroup.normalizer (L0 : Set G) :=
    mem_normalizer_of_barX_normalizes hp (H_le_M h) (L0_comp_H h) hcM hcH hcnorm
  have hcL1 : c ∈ Subgroup.normalizer ((L1of p M D L0 : Subgroup G) : Set G) :=
    mem_normalizer_iff_gLBConj_eq.2 (conj_L1_eq hcI hcL0)
  refine ⟨c, Subgroup.mem_inf.2 ⟨?_, ?_⟩, hc1, hcZ⟩
  · refine mem_centBar_of_comm_mod hp (L1_isSubnormal h) hcL1 hcB (fun x hx => ?_)
    have hxM : x ∈ M := (L1_le_istar h |>.trans (istar_le_M p M D)) hx
    have hx2 : x ∈ Sec13g.L2of p M D L0 := Sec13g.L1_le_L2 hx
    have hxv : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hxM⟩ ∈ barX p M (Sec13g.L2of p M D L0) :=
      (Lemma1311.mem_barX' p).2 ⟨⟨x, hxM⟩, hx2, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 hcc _ hxv
    exact mem_core_of_comm_bar hcM' hxM this.symm
  · exact Subgroup.mem_centralizer_singleton_iff.2 hdc.symm


theorem barX_comp_le_normalizer_V1 (h : Cex1310 G m p B M E A D T R L0 d) {L' : Subgroup G}
    (hL' : GLAPComponent p (Istar p M D) L') :
    barX p M L' ≤ Subgroup.normalizer ((barX p M (L1of p M D L0) :
      Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  rintro _ ⟨x, hx, rfl⟩
  have hxI : (x : G) ∈ Istar p M D := hL'.1 (Subgroup.mem_subgroupOf.1 hx)
  have h1 := barX_gLBConj_eq p x.2 (L1of p M D L0)
  rw [L1_conj_eq hxI] at h1
  exact mem_normalizer_iff_gLBConj_eq.2 h1.symm

theorem V1_le_normalizer_comp (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L)
    (hV : barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L))
    {L' : Subgroup G} (hL' : GLAPComponent p (Istar p M D) L') :
    barX p M (L1of p M D L0) ≤ Subgroup.normalizer ((barX p M L' : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have hp := prime_of h
  have hdM := d_mem_M h
  rw [hV]
  refine iSup_le fun i => ?_
  have hLi := istar_comp_conj hp hL (M.pow_mem hdM i)
  by_cases hEq : barX p M (GLBConj (d ^ (i : ℕ)) L) = barX p M L'
  · rw [hEq]
    exact Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (comm_of_comp (Lemma1311.isComponent_barX_of_pComp hp hLi)
      (Lemma1311.isComponent_barX_of_pComp hp hL') hEq x hx y hy).symm

theorem hall_of_a (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L)
    (hV : barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L))
    (ha : Prop139a p M D) :
    ∀ L', GLAPComponent p (Istar p M D) L' → barX p M L' ≤ barX p M (L1of p M D L0) := by
  have hp := prime_of h
  obtain ⟨hp3, hIoS, L1', hL1', hIL1', hr1, htyp⟩ := ha
  have hIL : Istar p M D = L1' := hIoS.symm.trans hIL1'
  have hL1'' : GLAPComponent p (Istar p M D) L1' := hIoS ▸ hL1'
  intro L' hL'
  have e1 := Lemma1311.pComp_eq_of_single hp hIL hL1'' hL'
  have e2 := Lemma1311.pComp_eq_of_single hp hIL hL1'' hL
  rw [e1, ← e2, hV]
  have := le_iSup (fun i : Fin p => barX p M (GLBConj (d ^ (i : ℕ)) L)) ⟨0, hp.pos⟩
  simpa [gLBConj_one] using this

abbrev CB (p : ℕ) (B M K : Subgroup G) : Subgroup G :=
  B ⊓ Lemma1311.KGof p M (Subgroup.centralizer
    ((barX p M K : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)))

theorem relIndex_CB_le (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d)
    {K : Subgroup G} (hK : GLAPComponent p (Istar p M D) K) : (CB p B M K).relIndex B ≤ p := by
  have hp := prime_of h
  obtain ⟨hbl, hBN, hdec, hint, hrk⟩ := block_data h133 h hK
  have hcard := card_B_inf h133 h hK
  have hsn : IsSubnormal K M := (istar_comp_M hp hK).2.1
  have hCT : centBar p B K ≤ CB p B M K := by
    intro b hb
    have hbB : b ∈ B := (Subgroup.mem_inf.1 hb).2
    have hbM : b ∈ M := B_le_M h hbB
    obtain ⟨-, hcomm⟩ := comm_mod_of_mem_centBar hp hsn hb
    refine ⟨hbB, (Lemma1311.mem_KGof p).2 ⟨hbM, ?_⟩⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    obtain ⟨x, hx, rfl⟩ := (Lemma1311.mem_barX' p).1 hv
    exact (comm_bar_of_mem_core hbM x.2 (hcomm x hx)).symm
  have hBel : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := fun x hx y hy => elemAbelian_comm (B_elem h) hx hy
  have := relIndex_le_of_dec hBel hdec inf_le_left inf_le_right hCT
  rw [hcard] at this
  exact this

theorem iInf_CB_eq_bot (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hV : barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L))
    (hN : CN p M D L0 ≤ GLAPPrimeCoreOf p M)
    (hall : ∀ L', GLAPComponent p (Istar p M D) L' →
      barX p M L' ≤ barX p M (L1of p M D L0)) :
    (⨅ i : Fin p, CB p B M (GLBConj (d ^ (i : ℕ)) L)) = ⊥ := by
  have hp := prime_of h
  rw [eq_bot_iff]
  intro b hb
  rw [Subgroup.mem_iInf] at hb
  have hbB : b ∈ B := (hb ⟨0, hp.pos⟩).1
  have hbM : b ∈ M := B_le_M h hbB
  have hbN : b ∈ CN p M D L0 := by
    refine (Lemma1311.mem_KGof p).2 ⟨hbM, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv1 : v ∈ barX p M (L1of p M D L0) := by
      have h1 : barX p M (Sec13g.L2of p M D L0) ≤ barX p M (Istar p M D) :=
        Lemma1311.barX_mono' p (L2_le_istar h)
      have h2 := Lemma1311.barX_istar_le_iSup_pComp hp M D
      have h3 : (⨆ y : {L' : Subgroup G // GLAPComponent p (Istar p M D) L'}, barX p M y.1) ≤
          barX p M (L1of p M D L0) := iSup_le fun y => hall y.1 y.2
      exact h3 (h2 (h1 hv))
    rw [hV] at hv1
    have hle : (⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L)) ≤
        Subgroup.centralizer ({QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨b, hbM⟩} :
          Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
      refine iSup_le fun i => ?_
      intro w hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨_, hbc⟩ := (Lemma1311.mem_KGof p).1 (hb i).2
      exact Subgroup.mem_centralizer_iff.1 hbc w hw
    exact Subgroup.mem_centralizer_singleton_iff.1 (hle hv1)
  have hbO : b ∈ GLAPPrimeCoreOf p M := hN hbN
  have hbot : B ⊓ GLAPPrimeCoreOf p M = ⊥ :=
    isPGroup_inf_eq_bot_of_not_dvd hp ((R_pgroup h).to_le (B_le_R h))
      (not_dvd_card_glaPPrimeCoreOf hp M)
  have : b ∈ B ⊓ GLAPPrimeCoreOf p M := ⟨hbB, hbO⟩
  rw [hbot] at this
  exact this

theorem count_false (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L)
    (hV : barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L))
    (hN : CN p M D L0 ≤ GLAPPrimeCoreOf p M)
    (hall : ∀ L', GLAPComponent p (Istar p M D) L' →
      barX p M L' ≤ barX p M (L1of p M D L0)) : False := by
  have hp := prime_of h
  have hdM := d_mem_M h
  have hm4 : 4 ≤ m := h.standing.four_le
  have hp1 := hp.one_lt
  have hT1 : ∀ i : Fin p, (CB p B M (GLBConj (d ^ (i : ℕ)) L)).relIndex B ≤ p :=
    fun i => relIndex_CB_le h133 h (istar_comp_conj hp hL (M.pow_mem hdM i))
  have hT2 := iInf_CB_eq_bot h hV hN hall
  have hBcard := B_card h
  rcases h.h139 with ha | hb
  ·
    obtain ⟨hp3, hIoS, L1', hL1', hIL1', hr1, htyp⟩ := ha
    have hIL : Istar p M D = L1' := hIoS.symm.trans hIL1'
    have hL1'' : GLAPComponent p (Istar p M D) L1' := hIoS ▸ hL1'
    have hKL : ∀ i : Fin p, GLBConj (d ^ (i : ℕ)) L = L := fun i =>
      (Lemma1311.pComp_eq_of_single hp hIL hL1'' (istar_comp_conj hp hL (M.pow_mem hdM i))).trans
        (Lemma1311.pComp_eq_of_single hp hIL hL1'' hL).symm
    have hT0 : CB p B M L = ⊥ := by
      rw [← hT2]
      refine le_antisymm (le_iInf fun i => by rw [hKL i]) ?_
      have := iInf_le (fun i : Fin p => CB p B M (GLBConj (d ^ (i : ℕ)) L)) ⟨0, hp.pos⟩
      simpa [gLBConj_one] using this
    have h1 := hT1 ⟨0, hp.pos⟩
    simp only [pow_zero, gLBConj_one] at h1
    rw [hT0, Subgroup.relIndex_bot_left, hBcard] at h1
    have h2 : p ^ 4 ≤ p ^ m := Nat.pow_le_pow_right hp.pos hm4
    have h3 : p ^ 4 = p * p ^ 3 := by ring
    have h4 : 2 ≤ p ^ 3 := by
      calc 2 ≤ p := hp1
        _ = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ 3 := Nat.pow_le_pow_right hp.pos (by norm_num)
    nlinarith
  ·
    obtain ⟨hp3, -⟩ := hb
    have hB1 := Subgroup.relIndex_iInf_le (L := B)
      (fun i : Fin p => CB p B M (GLBConj (d ^ (i : ℕ)) L))
    rw [hT2, Subgroup.relIndex_bot_left] at hB1
    have hprod : ∏ i : Fin p, (CB p B M (GLBConj (d ^ (i : ℕ)) L)).relIndex B ≤ p ^ p := by
      calc ∏ i : Fin p, (CB p B M (GLBConj (d ^ (i : ℕ)) L)).relIndex B ≤ ∏ _i : Fin p, p :=
            Finset.prod_le_prod₀ (fun i _ => Nat.zero_le _) (fun i _ => hT1 i)
        _ = p ^ p := by simp
    have hle : p ^ m ≤ p ^ p := by rw [← hBcard]; exact hB1.trans hprod
    have hmp : m ≤ p := (Nat.pow_le_pow_iff_right hp1).1 hle
    omega

theorem caseB' (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L)
    (hV : barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L))
    (hN : CN p M D L0 ≤ GLAPPrimeCoreOf p M) :
    ∃ c ∈ centBar p B (L1of p M D L0) ⊓ Cg d, c ≠ 1 ∧ (Prop139a p M D → c ∈ centerOf R) := by
  have hp := prime_of h
  have hp2 := ne_two_of h
  have hdM := d_mem_M h
  have hA : ¬ Prop139a p M D := fun ha => count_false h133 h hL hV hN (hall_of_a h hL hV ha)
  have hex : ∃ L', GLAPComponent p (Istar p M D) L' ∧
      ¬ barX p M L' ≤ barX p M (L1of p M D L0) := by
    by_contra hcon
    push Not at hcon
    exact count_false h133 h hL hV hN hcon
  obtain ⟨L', hL', hnot⟩ := hex
  let P : Subgroup G → Prop := fun L'' => ¬ barX p M L'' ≤ barX p M (L1of p M D L0)
  have hVd : GLBConj (dBar h) (barX p M (L1of p M D L0)) = barX p M (L1of p M D L0) := by
    have h1 := barX_gLBConj_eq p hdM (L1of p M D L0)
    rw [gLBConj_eq_of_mem_normalizer (d_mem_normalizer_L1 h)] at h1
    exact h1.symm
  have hcl : ∀ L'', GLAPComponent p (Istar p M D) L'' → P L'' → P (GLBConj d L'') := by
    intro L'' _ hP hle
    apply hP
    rw [barX_gLBConj_eq p hdM] at hle
    intro x hx
    have hy : (dBar h)⁻¹ * x * (dBar h) ∈ GLBConj (dBar h) (barX p M L'') := by
      rw [mem_gLBConj]
      have e : dBar h * ((dBar h)⁻¹ * x * dBar h) * (dBar h)⁻¹ = x := by group
      rw [e]
      exact hx
    have hy' := hle hy
    rw [← hVd, mem_gLBConj] at hy'
    have e : dBar h * ((dBar h)⁻¹ * x * dBar h) * (dBar h)⁻¹ = x := by group
    rw [e] at hy'
    exact hy'
  obtain ⟨c, hcE, hc1, hcd⟩ := exists_fixed_point h133 h P hcl ⟨L', hL', hnot⟩
  refine ⟨c, Subgroup.mem_inf.2 ⟨?_, Subgroup.mem_centralizer_singleton_iff.2 hcd.symm⟩, hc1,
    fun ha => absurd ha hA⟩
  have hle : joinB p B M D P ≤ centBar p B (L1of p M D L0) := by
    refine iSup₂_le fun L'' hL'' x hx => ?_
    obtain ⟨hxB, hxL⟩ := Subgroup.mem_inf.1 hx
    have hxI : x ∈ Istar p M D := hL''.1.1 hxL
    have hxM : x ∈ M := istar_le_M p M D hxI
    refine mem_centBar_of_comm_mod hp (L1_isSubnormal h) (istar_le_normalizer_L1 hxI) hxB
      (fun y hy => ?_)
    have hyM : y ∈ M := ((L1_le_istar h).trans (istar_le_M p M D)) hy
    have hxv : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hxM⟩ ∈ barX p M L'' :=
      (Lemma1311.mem_barX' p).2 ⟨⟨x, hxM⟩, hxL, rfl⟩
    have hyv : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨y, hyM⟩ ∈ barX p M (L1of p M D L0) :=
      (Lemma1311.mem_barX' p).2 ⟨⟨y, hyM⟩, hy, rfl⟩
    obtain ⟨hbl, -⟩ := block_data h133 h hL''.1
    have hcomm := commute_of_not_le (barX_simple hp hp2 (istar_comp_M hp hL''.1) hbl)
      (barX_comp_le_normalizer_V1 h hL''.1) (V1_le_normalizer_comp h hL hV hL''.1) hL''.2 _ hxv _ hyv
    exact mem_core_of_comm_bar hxM hyM hcomm
  exact hle hcE

theorem hcB_holds (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L)
    (hV : barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L)) :
    ∃ c ∈ centBar p B (L1of p M D L0) ⊓ Cg d, c ≠ 1 ∧ (Prop139a p M D → c ∈ centerOf R) := by
  by_cases hN : CN p M D L0 ≤ GLAPPrimeCoreOf p M
  · exact caseB' h133 h hL hV hN
  · obtain ⟨c, hc, hc1, hcZ⟩ := caseA' h hN
    exact ⟨c, hc, hc1, fun _ => hcZ⟩


theorem V_eq_iSup (h : Cex1310 G m p B M E A D T R L0 d) :
    barX p M (Istar p M D) =
      ⨆ y : {L : Subgroup G // GLAPComponent p (Istar p M D) L}, barX p M y.1 := by
  refine le_antisymm (Lemma1311.barX_istar_le_iSup_pComp (prime_of h) M D) (iSup_le fun y => ?_)
  exact Lemma1311.barX_mono' p y.2.1

theorem V_center (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) :
    ∀ z ∈ barX p M (Istar p M D), (∀ y ∈ barX p M (Istar p M D), z * y = y * z) → z = 1 := by
  have hp := prime_of h
  have hp2 := ne_two_of h
  haveI : Fintype {L : Subgroup G // GLAPComponent p (Istar p M D) L} := Fintype.ofFinite _
  rw [V_eq_iSup h]
  refine center_iSup_eq_one
    (fun y : {L : Subgroup G // GLAPComponent p (Istar p M D) L} => barX p M y.1) ?_ ?_
  · intro i j hij x hx y hy
    exact comm_of_comp (Lemma1311.isComponent_barX_of_pComp hp i.2)
      (Lemma1311.isComponent_barX_of_pComp hp j.2) hij x hx y hy
  · intro i x hx hc
    obtain ⟨hbl, -⟩ := block_data h133 h i.2
    exact barX_centerless hp hp2 (istar_comp_M hp i.2) hbl x hx hc

theorem V_le_normalizer_comp (h : Cex1310 G m p B M E A D T R L0 d) {L' : Subgroup G}
    (hL' : GLAPComponent p (Istar p M D) L') :
    barX p M (Istar p M D) ≤ Subgroup.normalizer ((barX p M L' : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  have hp := prime_of h
  rw [V_eq_iSup h]
  refine iSup_le fun y => ?_
  by_cases hEq : barX p M y.1 = barX p M L'
  · rw [hEq]
    exact Subgroup.le_normalizer
  · refine le_trans ?_ (Subgroup.centralizer_le_normalizer _)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact (comm_of_comp (Lemma1311.isComponent_barX_of_pComp hp y.2)
      (Lemma1311.isComponent_barX_of_pComp hp hL') hEq x hx z hz).symm

theorem V_le_normalizer_V1 (h : Cex1310 G m p B M E A D T R L0 d) :
    barX p M (Istar p M D) ≤ Subgroup.normalizer ((barX p M (L1of p M D L0) :
      Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  rw [V_eq_iSup h]
  exact iSup_le fun y => barX_comp_le_normalizer_V1 h y.2


theorem V1_conj_dbar (h : Cex1310 G m p B M E A D T R L0 d) (i : ℕ) :
    GLBConj ((dBar h) ^ i) (barX p M (L1of p M D L0)) = barX p M (L1of p M D L0) := by
  rw [← barX_conj_pow h _ i]
  rw [gLBConj_eq_of_mem_normalizer
    ((Subgroup.normalizer ((L1of p M D L0 : Subgroup G) : Set G)).pow_mem (d_mem_normalizer_L1 h) i)]

theorem V1_le_V (h : Cex1310 G m p B M E A D T R L0 d) :
    barX p M (L1of p M D L0) ≤ barX p M (Istar p M D) :=
  Lemma1311.barX_mono' p (L1_le_istar h)

theorem barX_L0_ne_bot (h : Cex1310 G m p B M E A D T R L0 d) : barX p M L0 ≠ ⊥ := by
  have hp := prime_of h
  intro h0
  have hne : barX p (Istar p M D ⊓ Cg d) L0 ≠ ⊥ := isComponentOf_ne_bot' (L0_comp_H h).2.2.1
  apply hne
  rw [eq_bot_iff]
  rintro _ ⟨x, hx, rfl⟩
  have hxL : (x : G) ∈ L0 := Subgroup.mem_subgroupOf.1 hx
  have hxM : (x : G) ∈ M := H_le_M h x.2
  have h1 : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hxM⟩ = 1 := by
    have : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hxM⟩ ∈ barX p M L0 :=
      (Lemma1311.mem_barX' p).2 ⟨⟨x, hxM⟩, hxL, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    exact this
  have hxO : (x : G) ∈ GLAPPrimeCoreOf p M := ⟨⟨x, hxM⟩, (QuotientGroup.eq_one_iff _).1 h1, rfl⟩
  have hxO' : (x : G) ∈ GLAPPrimeCoreOf p (Istar p M D ⊓ Cg d) :=
    inf_glaPPrimeCoreOf_le hp (H_le_M h) ⟨x.2, hxO⟩
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff x).2 (by
    obtain ⟨z, hz, hzeq⟩ := hxO'
    have : z = x := Subtype.ext hzeq
    rwa [← this])

theorem exists_comp_le_V1 (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) :
    ∃ L', GLAPComponent p (Istar p M D) L' ∧ barX p M L' ≤ barX p M (L1of p M D L0) := by
  have hp := prime_of h
  have hp2 := ne_two_of h
  by_contra hcon
  push Not at hcon
  have hcentral : ∀ v ∈ barX p M (L1of p M D L0), v = 1 := by
    intro v hv
    have hvV := V1_le_V h hv
    have hle : barX p M (Istar p M D) ≤ Subgroup.centralizer ({v} : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
      rw [V_eq_iSup h]
      refine iSup_le fun y => ?_
      intro k hk
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨hbl, -⟩ := block_data h133 h y.2
      exact commute_of_not_le (barX_simple hp hp2 (istar_comp_M hp y.2) hbl)
        (barX_comp_le_normalizer_V1 h y.2) ((V1_le_V h).trans (V_le_normalizer_comp h y.2))
        (hcon y.1 y.2) k hk v hv
    exact V_center h133 h v hvV (fun y hy => (Subgroup.mem_centralizer_singleton_iff.1 (hle hy)).symm)
  apply barX_L0_ne_bot h
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact hcentral x (Lemma1311.barX_mono' p Sec13g.le_L1of hx)


noncomputable abbrev Worb (p : ℕ) (M D : Subgroup G) (d : G) (L : Subgroup G) :
    Subgroup (↥M ⧸ GLAPPrimeCore p ↥M) :=
  ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L)

theorem comp_conj_pow (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) (i : ℕ) :
    GLAPComponent p (Istar p M D) (GLBConj (d ^ i) L) :=
  istar_comp_conj (prime_of h) hL (M.pow_mem (d_mem_M h) i)

theorem Worb_le_V1 (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hLV : barX p M L ≤ barX p M (L1of p M D L0)) :
    Worb p M D d L ≤ barX p M (L1of p M D L0) := by
  refine iSup_le fun i => ?_
  rw [barX_conj_pow h L i, ← V1_conj_dbar h i]
  exact gLBConj_mono _ hLV

theorem Worb_le_V (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) : Worb p M D d L ≤ barX p M (Istar p M D) :=
  iSup_le fun i => Lemma1311.barX_mono' p (comp_conj_pow h hL i).1

theorem Worb_conj_eq (h : Cex1310 G m p B M E A D T R L0 d) (L : Subgroup G) :
    GLBConj (dBar h) (Worb p M D d L) = Worb p M D d L := by
  have hdM := d_mem_M h
  have hle : GLBConj (dBar h) (Worb p M D d L) ≤ Worb p M D d L := by
    unfold Worb
    rw [gLBConj_iSup_eq]
    refine iSup_le fun i => ?_
    have h1 : GLBConj (dBar h) (barX p M (GLBConj (d ^ (i : ℕ)) L)) =
        barX p M (GLBConj d (GLBConj (d ^ (i : ℕ)) L)) := (barX_gLBConj_eq p hdM _).symm
    rw [h1]
    obtain ⟨j, hj⟩ := orbit_closed h L _ ⟨i, rfl⟩
    rw [hj]
    exact le_iSup (fun i : Fin p => barX p M (GLBConj (d ^ (i : ℕ)) L)) j
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_gLBConj]

theorem V_le_normalizer_Worb (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) :
    barX p M (Istar p M D) ≤ Subgroup.normalizer ((Worb p M D d L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold Worb
  rw [gLBConj_iSup_eq]
  refine iSup_congr fun i => ?_
  exact gLBConj_eq_of_mem_normalizer (V_le_normalizer_comp h (comp_conj_pow h hL i) hg)

theorem Worb_center (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) :
    ∀ z ∈ Worb p M D d L, (∀ y ∈ Worb p M D d L, z * y = y * z) → z = 1 := by
  have hp := prime_of h
  have hp2 := ne_two_of h
  unfold Worb
  refine center_iSup_eq_one (fun i : Fin p => barX p M (GLBConj (d ^ (i : ℕ)) L)) ?_ ?_
  · intro i j hij x hx y hy
    exact comm_of_comp (Lemma1311.isComponent_barX_of_pComp hp (comp_conj_pow h hL i))
      (Lemma1311.isComponent_barX_of_pComp hp (comp_conj_pow h hL j)) hij x hx y hy
  · intro i x hx hc
    obtain ⟨hbl, -⟩ := block_data h133 h (comp_conj_pow h hL i)
    exact barX_centerless hp hp2 (istar_comp_M hp (comp_conj_pow h hL i)) hbl x hx hc

noncomputable abbrev Yorb (p : ℕ) (M D L0 : Subgroup G) (d : G) (L : Subgroup G) :
    Subgroup (↥M ⧸ GLAPPrimeCore p ↥M) :=
  barX p M (L1of p M D L0) ⊓ Subgroup.centralizer ((Worb p M D d L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
    Set (↥M ⧸ GLAPPrimeCore p ↥M))

theorem Yorb_conj_eq (h : Cex1310 G m p B M E A D T R L0 d) (L : Subgroup G) :
    GLBConj (dBar h) (Yorb p M D L0 d L) = Yorb p M D L0 d L := by
  unfold Yorb
  rw [gLBConj_inf, gLBConj_centralizer, Worb_conj_eq h L]
  have := V1_conj_dbar h 1
  rw [pow_one] at this
  rw [this]

theorem V_le_normalizer_Yorb (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) :
    barX p M (Istar p M D) ≤ Subgroup.normalizer ((Yorb p M D L0 d L : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)) :
      Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
  intro g hg
  rw [mem_normalizer_iff_gLBConj_eq]
  unfold Yorb
  rw [gLBConj_inf, gLBConj_centralizer,
    gLBConj_eq_of_mem_normalizer (V_le_normalizer_Worb h hL hg),
    gLBConj_eq_of_mem_normalizer (V_le_normalizer_V1 h hg)]

theorem Worb_inf_Yorb (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) : Worb p M D d L ⊓ Yorb p M D L0 d L = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  refine Worb_center h133 h hL z hz.1 (fun y hy => ?_)
  exact (Subgroup.mem_centralizer_iff.1 hz.2.2 y hy).symm

theorem Worb_comm_Yorb (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G} :
    ∀ w ∈ Worb p M D d L, ∀ y ∈ Yorb p M D L0 d L, w * y = y * w := fun w hw y hy =>
  Subgroup.mem_centralizer_iff.1 hy.2 w hw

theorem V1_le_Worb_mul_Yorb (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d)
    {L : Subgroup G} (hL : GLAPComponent p (Istar p M D) L)
    (hLV : barX p M L ≤ barX p M (L1of p M D L0)) :
    ∀ v ∈ barX p M (L1of p M D L0), ∃ w ∈ Worb p M D d L, ∃ y ∈ Yorb p M D L0 d L, w * y = v := by
  have hp := prime_of h
  have hp2 := ne_two_of h
  intro v hv
  set W := Worb p M D d L with hW
  set Vc : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M) :=
    ⨆ (y : {L' : Subgroup G // GLAPComponent p (Istar p M D) L'}) (_ : ¬ barX p M y.1 ≤ W),
      barX p M y.1 with hVc
  have hVcC : Vc ≤ Subgroup.centralizer (W : Set (↥M ⧸ GLAPPrimeCore p ↥M)) := by
    refine iSup₂_le fun y hy => ?_
    obtain ⟨hbl, -⟩ := block_data h133 h y.2
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact (commute_of_not_le (barX_simple hp hp2 (istar_comp_M hp y.2) hbl)
      ((Lemma1311.barX_mono' p y.2.1).trans (V_le_normalizer_Worb h hL))
      ((Worb_le_V h hL).trans (V_le_normalizer_comp h y.2)) hy k hk w hw).symm
  have hV : barX p M (Istar p M D) ≤ W ⊔ Vc := by
    rw [V_eq_iSup h]
    refine iSup_le fun y => ?_
    by_cases hy : barX p M y.1 ≤ W
    · exact hy.trans le_sup_left
    · exact (le_iSup₂_of_le (f := fun (y : {L' : Subgroup G // GLAPComponent p (Istar p M D) L'})
        (_ : ¬ barX p M y.1 ≤ W) => barX p M y.1) y hy le_rfl).trans le_sup_right
  obtain ⟨w, hw, c, hc, hwc⟩ := exists_mul_of_mem_sup_of_commute
    (fun x hx y hy => Subgroup.mem_centralizer_iff.1 (hVcC hy) x hx) (hV (V1_le_V h hv))
  refine ⟨w, hw, c, ⟨?_, hVcC hc⟩, hwc⟩
  have hwV1 : w ∈ barX p M (L1of p M D L0) := Worb_le_V1 h hLV hw
  have : c = w⁻¹ * v := by rw [← hwc]; group
  rw [this]
  exact (barX p M (L1of p M D L0)).mul_mem ((barX p M (L1of p M D L0)).inv_mem hwV1) hv


theorem bar_eq_of_bar_eq (hp : p.Prime) {H : Subgroup G} (hHM : H ≤ M) {x y : G} (hx : x ∈ H)
    (hy : y ∈ H)
    (h : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨x, hHM hx⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨y, hHM hy⟩) :
    QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨x, hx⟩ = QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨y, hy⟩ := by
  have h1 := (QuotientGroup.eq).1 h
  have h2 : x⁻¹ * y ∈ GLAPPrimeCoreOf p M := ⟨_, h1, by simp⟩
  have h3 : x⁻¹ * y ∈ GLAPPrimeCoreOf p H :=
    inf_glaPPrimeCoreOf_le hp hHM ⟨H.mul_mem (H.inv_mem hx) hy, h2⟩
  obtain ⟨z, hz, hzeq⟩ := h3
  refine (QuotientGroup.eq).2 ?_
  have : z = (⟨x, hx⟩ : ↥H)⁻¹ * ⟨y, hy⟩ := Subtype.ext (by simpa using hzeq)
  rw [← this]
  exact hz

theorem exists_pElem_L0 (h : Cex1310 G m p B M E A D T R L0 d) : ∃ s ∈ L0, s ≠ 1 ∧ s ^ p = 1 := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hno
  push Not at hno
  have hndvd : ¬ p ∣ Nat.card ↥L0 := by
    intro hdvd
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hord : orderOf (g : G) = p := by rw [Subgroup.orderOf_coe]; exact hg
    have hs1 : (g : G) ≠ 1 := fun h1 => by
      rw [h1, orderOf_one] at hord
      exact hp.one_lt.ne hord
    exact hno (g : G) g.2 hs1 (by rw [← hord]; exact pow_orderOf_eq_one _)
  have hcop : Nat.Coprime p (Nat.card ↥L0) := (Nat.Prime.coprime_iff_not_dvd hp).2 hndvd
  have hL0H := L0_comp_H h
  have hdvdK : Nat.card ↥(barX p (Istar p M D ⊓ Cg d) L0) ∣ Nat.card ↥L0 := by
    have h1 := Subgroup.card_map_dvd (QuotientGroup.mk' (GLAPPrimeCore p ↥(Istar p M D ⊓ Cg d)))
      (H := L0.subgroupOf (Istar p M D ⊓ Cg d))
    have h2 : Nat.card ↥(L0.subgroupOf (Istar p M D ⊓ Cg d)) = Nat.card ↥L0 :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL0H.1).toEquiv
    rw [h2] at h1
    exact h1
  have hcopK := Nat.Coprime.coprime_dvd_right hdvdK hcop
  have hbot : barX p (Istar p M D ⊓ Cg d) L0 = ⊥ :=
    Lemma1311.eq_bot_of_subnormal_pPrime hp (Lemma1311.glaPPrimeCore_quot_eq_bot p ↥(Istar p M D ⊓ Cg d))
      hL0H.2.2.1.2.1 hcopK
  exact isComponentOf_ne_bot' hL0H.2.2.1 hbot

theorem simple_barX_L0 (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d)
    {L : Subgroup G} (hL : GLAPComponent p (Istar p M D) L) :
    IsSimpleGroup ↥(barX p (Istar p M D ⊓ Cg d) L0) := by
  have hp := prime_of h
  have hp2 := ne_two_of h
  obtain ⟨e⟩ := h.hL0iso L hL
  obtain ⟨hbl, -⟩ := block_data h133 h hL
  have hLM := istar_comp_M hp hL
  have e1 : ↥(barX p (Istar p M D ⊓ Cg d) L0) ≃* barOf p L0 :=
    Lemma1311.barXIso hp (L0_comp_H h).1 (L0_comp_H h).2.1
  have e2 : ↥(barX p M L) ≃* barOf p L := Lemma1311.barXIso hp hLM.1 hLM.2.1
  exact (e1.trans (e.trans e2.symm)).isSimpleGroup_congr.2 (barX_simple hp hp2 hLM hbl)

theorem L0_le_of_pElems (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d)
    {L : Subgroup G} (hL : GLAPComponent p (Istar p M D) L) {T₀ : Subgroup G}
    (hTH : T₀ ≤ Istar p M D ⊓ Cg d)
    (hTn : ∀ g ∈ Istar p M D ⊓ Cg d, ∀ t ∈ T₀, g * t * g⁻¹ ∈ T₀)
    (hpel : ∀ s ∈ L0, ∀ k : ℕ, s ^ (p ^ k) = 1 → s ∈ T₀) : L0 ≤ T₀ := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  set H := Istar p M D ⊓ Cg d with hH
  have hL0H : GLAPComponent p H L0 := L0_comp_H h
  have hL0le : L0 ≤ H := hL0H.1
  have hsimple := simple_barX_L0 h133 h hL
  by_contra hnot
  have hJlt : L0 ⊓ T₀ < L0 := by
    refine lt_of_le_of_ne inf_le_left (fun heq => hnot ?_)
    rw [← heq]
    exact inf_le_right
  have hTnorm : ∀ g ∈ H, g ∈ Subgroup.normalizer (T₀ : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro t
    refine ⟨fun ht => hTn g hg t ht, fun ht => ?_⟩
    have := hTn g⁻¹ (H.inv_mem hg) _ ht
    simpa [mul_assoc] using this
  have hJn : ((L0 ⊓ T₀).subgroupOf L0).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2 ?_
    intro g hg
    exact mem_normalizer_inf (Subgroup.le_normalizer hg) (hTnorm g (hL0le hg))
  have hJsn : IsSubnormal (L0 ⊓ T₀) H := IsSubnormal.step inf_le_left hJn hL0H.2.1
  have hJc : ∀ y ∈ L0, ∀ x ∈ L0 ⊓ T₀, y * x * y⁻¹ ∈ L0 ⊓ T₀ := by
    intro y hy x hx
    have := hJn.conj_mem ⟨x, hx.1⟩ (Subgroup.mem_subgroupOf.2 hx) ⟨y, hy⟩
    simpa using Subgroup.mem_subgroupOf.1 this
  have hbar : barX p H (L0 ⊓ T₀) = barX p H L0 := by
    refine le_antisymm (Lemma1311.barX_mono' p inf_le_left) ?_
    haveI : IsSimpleGroup ↥(barX p H L0) := hsimple
    set N : Subgroup ↥(barX p H L0) := (barX p H (L0 ⊓ T₀)).subgroupOf (barX p H L0) with hN
    haveI : N.Normal := by
      constructor
      intro n hn g
      obtain ⟨x, hxJ, hx⟩ := (Lemma1311.mem_barX' p).1 (Subgroup.mem_subgroupOf.1 hn)
      obtain ⟨y, hyL, hy⟩ := (Lemma1311.mem_barX' p).1 g.2
      refine Subgroup.mem_subgroupOf.2 ((Lemma1311.mem_barX' p).2 ⟨y * x * y⁻¹, ?_, ?_⟩)
      · have := hJc (y : G) hyL (x : G) hxJ
        simpa using this
      · rw [map_mul, map_mul, map_inv, hx, hy]
        simp
    obtain ⟨s, hsL, hs1, hsp⟩ := exists_pElem_L0 h
    have hsT : s ∈ T₀ := hpel s hsL 1 (by simpa using hsp)
    have hsJ : s ∈ L0 ⊓ T₀ := ⟨hsL, hsT⟩
    have hsH : s ∈ H := hL0le hsL
    set sb : ↥(barX p H L0) := ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨s, hsH⟩,
      (Lemma1311.mem_barX' p).2 ⟨⟨s, hsH⟩, hsL, rfl⟩⟩ with hsb
    have hsbN : sb ∈ N := Subgroup.mem_subgroupOf.2 ((Lemma1311.mem_barX' p).2 ⟨⟨s, hsH⟩, hsJ, rfl⟩)
    have hsb1 : sb ≠ 1 := by
      intro h1
      have h2 : QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨s, hsH⟩ = 1 := congrArg Subtype.val h1
      have h3 : (⟨s, hsH⟩ : ↥H) ∈ GLAPPrimeCore p ↥H := (QuotientGroup.eq_one_iff _).1 h2
      have hord : orderOf s = p := orderOf_eq_prime hsp hs1
      have h4 : s ∈ GLAPPrimeCoreOf p H := ⟨_, h3, rfl⟩
      have h5 : orderOf s ∣ Nat.card ↥(GLAPPrimeCoreOf p H) := by
        have := orderOf_dvd_natCard (⟨s, h4⟩ : ↥(GLAPPrimeCoreOf p H))
        simpa [Subgroup.orderOf_coe] using this
      rw [hord] at h5
      exact not_dvd_card_glaPPrimeCoreOf hp H h5
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h0 | h0
    · exfalso
      rw [h0, Subgroup.mem_bot] at hsbN
      exact hsb1 hsbN
    · intro k hk
      have : (⟨k, hk⟩ : ↥(barX p H L0)) ∈ N := by
        rw [h0]
        exact Subgroup.mem_top _
      exact Subgroup.mem_subgroupOf.1 this
  exact hL0H.2.2.2 _ hJlt hJsn hbar


theorem Tsub_normal (h : Cex1310 G m p B M E A D T R L0 d) {Z : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)}
    (hZ : barX p M (Istar p M D) ≤ Subgroup.normalizer (Z : Set (↥M ⧸ GLAPPrimeCore p ↥M))) :
    ∀ g ∈ Istar p M D ⊓ Cg d, ∀ t ∈ (Istar p M D ⊓ Cg d) ⊓ Lemma1311.KGof p M Z,
      g * t * g⁻¹ ∈ (Istar p M D ⊓ Cg d) ⊓ Lemma1311.KGof p M Z := by
  intro g hg t ht
  obtain ⟨htH, htK⟩ := ht
  obtain ⟨htM, htZ⟩ := (Lemma1311.mem_KGof p).1 htK
  have hgM : g ∈ M := H_le_M h hg
  have hgtM : g * t * g⁻¹ ∈ M := M.mul_mem (M.mul_mem hgM htM) (M.inv_mem hgM)
  refine ⟨(Istar p M D ⊓ Cg d).mul_mem ((Istar p M D ⊓ Cg d).mul_mem hg htH)
    ((Istar p M D ⊓ Cg d).inv_mem hg), (Lemma1311.mem_KGof p).2 ⟨hgtM, ?_⟩⟩
  have hgV : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩ ∈ barX p M (Istar p M D) :=
    (Lemma1311.mem_barX' p).2 ⟨⟨g, hgM⟩, hg.1, rfl⟩
  have := (Subgroup.mem_normalizer_iff.1 (hZ hgV) _).1 htZ
  have e : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g * t * g⁻¹, hgtM⟩ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩ * QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨t, htM⟩ *
        (QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨g, hgM⟩)⁻¹ := by
    simp only [← map_inv, ← map_mul]
    rfl
  rw [e]
  exact this

theorem normalizer_of_conj_closed {H T₀ : Subgroup G} (hTn : ∀ g ∈ H, ∀ t ∈ T₀, g * t * g⁻¹ ∈ T₀) :
    ∀ g ∈ H, g ∈ Subgroup.normalizer (T₀ : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro t
  refine ⟨fun ht => hTn g hg t ht, fun ht => ?_⟩
  have := hTn g⁻¹ (H.inv_mem hg) _ ht
  simpa [mul_assoc] using this

theorem L0_le_of_bar_le (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) {T₀ : Subgroup G} (hTH : T₀ ≤ Istar p M D ⊓ Cg d)
    (hTn : ∀ g ∈ Istar p M D ⊓ Cg d, ∀ t ∈ T₀, g * t * g⁻¹ ∈ T₀)
    (hle : barX p (Istar p M D ⊓ Cg d) L0 ≤ barX p (Istar p M D ⊓ Cg d) T₀) : L0 ≤ T₀ := by
  have hp := prime_of h
  refine L0_le_of_pElems h133 h hL hTH hTn (fun s hs k hsk => ?_)
  have hsH : s ∈ Istar p M D ⊓ Cg d := L0_le h hs
  obtain ⟨j, hj, hjn⟩ := exists_of_barX_le hle hs hsH
  have hpre : s ∈ preimBarX p (Istar p M D ⊓ Cg d) T₀ := mem_preimBarX_of_mul hj (hTH hj) hsH hjn
  have hnormal : (T₀.subgroupOf (preimBarX p (Istar p M D ⊓ Cg d) T₀)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (le_preimBarX p hTH)).2
      (fun x hx => normalizer_of_conj_closed hTn x (preimBarX_le p _ _ hx))
  exact mem_of_pPower_of_normal_preim hp hTH hnormal hpre hsk

theorem bar_L0_le_of_le {Z : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)}
    (hLT : L0 ≤ (Istar p M D ⊓ Cg d) ⊓ Lemma1311.KGof p M Z) : barX p M L0 ≤ Z := by
  rintro _ ⟨x, hx, rfl⟩
  obtain ⟨hM, hmem⟩ := (Lemma1311.mem_KGof p).1 (hLT (Subgroup.mem_subgroupOf.1 hx)).2
  exact hmem

theorem exists_decomp (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) (hLV : barX p M L ≤ barX p M (L1of p M D L0)) {l : G}
    (hl : l ∈ L0) :
    ∃ t ∈ (Istar p M D ⊓ Cg d) ⊓ Lemma1311.KGof p M (Worb p M D d L),
      ∃ t' ∈ (Istar p M D ⊓ Cg d) ⊓ Lemma1311.KGof p M (Yorb p M D L0 d L),
        (t * t')⁻¹ * l ∈ GLAPPrimeCoreOf p (Istar p M D ⊓ Cg d) := by
  have hp := prime_of h
  have hdM := d_mem_M h
  have hHM := H_le_M h
  have hlH : l ∈ Istar p M D ⊓ Cg d := L0_le h hl
  have hlM : l ∈ M := hHM hlH
  have hlb : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨l, hlM⟩ ∈ barX p M (L1of p M D L0) :=
    (Lemma1311.mem_barX' p).2 ⟨⟨l, hlM⟩, Sec13g.le_L1of hl, rfl⟩
  obtain ⟨w, hw, y, hy, hwy⟩ := V1_le_Worb_mul_Yorb h133 h hL hLV _ hlb
  have hdl : l * d = d * l := Subgroup.mem_centralizer_singleton_iff.1 hlH.2
  have hlbd : dBar h * QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨l, hlM⟩ * (dBar h)⁻¹ =
      QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨l, hlM⟩ := by
    have e : (⟨d, hdM⟩ : ↥M) * ⟨l, hlM⟩ = ⟨l, hlM⟩ * ⟨d, hdM⟩ := Subtype.ext hdl.symm
    unfold dBar
    rw [mul_inv_eq_iff_eq_mul, ← map_mul, ← map_mul, e]
  have hwconj : dBar h * w * (dBar h)⁻¹ ∈ Worb p M D d L := by
    have : w ∈ GLBConj (dBar h) (Worb p M D d L) := by rw [Worb_conj_eq h L]; exact hw
    exact mem_gLBConj.1 this
  have hyconj : dBar h * y * (dBar h)⁻¹ ∈ Yorb p M D L0 d L := by
    have : y ∈ GLBConj (dBar h) (Yorb p M D L0 d L) := by rw [Yorb_conj_eq h L]; exact hy
    exact mem_gLBConj.1 this
  have hprod : (dBar h * w * (dBar h)⁻¹) * (dBar h * y * (dBar h)⁻¹) = w * y := by
    calc (dBar h * w * (dBar h)⁻¹) * (dBar h * y * (dBar h)⁻¹) = dBar h * (w * y) * (dBar h)⁻¹ := by group
      _ = dBar h * QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨l, hlM⟩ * (dBar h)⁻¹ := by rw [hwy]
      _ = QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨l, hlM⟩ := hlbd
      _ = w * y := hwy.symm
  obtain ⟨hw', hy'⟩ := factor_unique (Worb_inf_Yorb h133 h hL) hwconj hw hyconj hy hprod
  have hbH := barX_inf_centralizer hp hdM (istar_le_M p M D) (d_mem_normalizer_istar h) (d_isPGroup h)
  have hwcomm : w * dBar h = dBar h * w := by
    have := congrArg (· * dBar h) hw'
    simpa [mul_assoc] using this.symm
  have hycomm : y * dBar h = dBar h * y := by
    have := congrArg (· * dBar h) hy'
    simpa [mul_assoc] using this.symm
  have hwH : w ∈ barX p M (Istar p M D ⊓ Cg d) := by
    rw [hbH]
    exact ⟨Worb_le_V h hL hw, Subgroup.mem_centralizer_singleton_iff.2 hwcomm⟩
  have hyH : y ∈ barX p M (Istar p M D ⊓ Cg d) := by
    rw [hbH]
    exact ⟨V1_le_V h hy.1, Subgroup.mem_centralizer_singleton_iff.2 hycomm⟩
  obtain ⟨t₁, ht₁H, ht₁⟩ := (Lemma1311.mem_barX' p).1 hwH
  obtain ⟨t₂, ht₂H, ht₂⟩ := (Lemma1311.mem_barX' p).1 hyH
  have hH' : ((t₁ : G) * (t₂ : G)) ∈ Istar p M D ⊓ Cg d :=
    (Istar p M D ⊓ Cg d).mul_mem ht₁H ht₂H
  refine ⟨t₁, ⟨ht₁H, (Lemma1311.mem_KGof p).2 ⟨t₁.2, ?_⟩⟩, t₂,
    ⟨ht₂H, (Lemma1311.mem_KGof p).2 ⟨t₂.2, ?_⟩⟩, ?_⟩
  · have : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨(t₁ : G), t₁.2⟩ = w := ht₁
    rw [this]
    exact hw
  · have : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨(t₂ : G), t₂.2⟩ = y := ht₂
    rw [this]
    exact hy
  · have hmk : QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨(t₁ : G) * t₂, M.mul_mem t₁.2 t₂.2⟩ =
        QuotientGroup.mk' (GLAPPrimeCore p ↥M) ⟨l, hlM⟩ := by
      have e : (⟨(t₁ : G) * t₂, M.mul_mem t₁.2 t₂.2⟩ : ↥M) = t₁ * t₂ := rfl
      rw [e, map_mul, ht₁, ht₂, hwy]
    have h1 := (QuotientGroup.eq).1 hmk
    have h2 : ((t₁ : G) * t₂)⁻¹ * l ∈ GLAPPrimeCoreOf p M := ⟨_, h1, by simp⟩
    exact inf_glaPPrimeCoreOf_le hp hHM
      ⟨(Istar p M D ⊓ Cg d).mul_mem ((Istar p M D ⊓ Cg d).inv_mem hH') hlH, h2⟩


theorem L0_support (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) {L : Subgroup G}
    (hL : GLAPComponent p (Istar p M D) L) (hLV : barX p M L ≤ barX p M (L1of p M D L0)) :
    barX p M L0 ≤ Worb p M D d L ∨ barX p M L0 ≤ Yorb p M D L0 d L := by
  have hp := prime_of h
  haveI : Fact p.Prime := ⟨hp⟩
  have hHM := H_le_M h
  have hL0H : GLAPComponent p (Istar p M D ⊓ Cg d) L0 := L0_comp_H h
  set H : Subgroup G := Istar p M D ⊓ Cg d with hH
  set T : Subgroup G := H ⊓ Lemma1311.KGof p M (Worb p M D d L) with hT
  set T' : Subgroup G := H ⊓ Lemma1311.KGof p M (Yorb p M D L0 d L) with hT'
  have hTn : ∀ g ∈ H, ∀ t ∈ T, g * t * g⁻¹ ∈ T := Tsub_normal h (V_le_normalizer_Worb h hL)
  have hT'n : ∀ g ∈ H, ∀ t ∈ T', g * t * g⁻¹ ∈ T' := Tsub_normal h (V_le_normalizer_Yorb h hL)
  have hNT : (barX p H T).Normal := by
    have hn : (T.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2
        (fun g hg => normalizer_of_conj_closed hTn g hg)
    exact Subgroup.Normal.map hn _ (QuotientGroup.mk'_surjective _)
  have hNT' : (barX p H T').Normal := by
    have hn : (T'.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).2
        (fun g hg => normalizer_of_conj_closed hT'n g hg)
    exact Subgroup.Normal.map hn _ (QuotientGroup.mk'_surjective _)
  have hcomm : ∀ a ∈ barX p H T, ∀ b ∈ barX p H T', a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, rfl⟩ := (Lemma1311.mem_barX' p).1 ha
    obtain ⟨y, hy, rfl⟩ := (Lemma1311.mem_barX' p).1 hb
    have hxT : (x : G) ∈ T := hx
    have hyT : (y : G) ∈ T' := hy
    obtain ⟨hxM, hxW⟩ := (Lemma1311.mem_KGof p).1 hxT.2
    obtain ⟨hyM, hyY⟩ := (Lemma1311.mem_KGof p).1 hyT.2
    have hq := Worb_comm_Yorb h _ hxW _ hyY
    have h1 := mem_core_of_comm_bar hxM hyM hq
    have h2 : ((x : G) * y * (x : G)⁻¹)⁻¹ * y ∈ GLAPPrimeCoreOf p H :=
      inf_glaPPrimeCoreOf_le hp hHM
        ⟨H.mul_mem (H.inv_mem (H.mul_mem (H.mul_mem x.2 y.2) (H.inv_mem x.2))) y.2, h1⟩
    exact comm_bar_of_mem_core x.2 y.2 h2
  have hprod : ∀ k ∈ barX p H L0, ∃ a ∈ barX p H T, ∃ b ∈ barX p H T', k = a * b := by
    intro k hk
    obtain ⟨x, hx, rfl⟩ := (Lemma1311.mem_barX' p).1 hk
    obtain ⟨t, ht, t', ht', hn⟩ := exists_decomp h133 h hL hLV hx
    refine ⟨QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨t, ht.1⟩,
      (Lemma1311.mem_barX' p).2 ⟨⟨t, ht.1⟩, ht, rfl⟩,
      QuotientGroup.mk' (GLAPPrimeCore p ↥H) ⟨t', ht'.1⟩,
      (Lemma1311.mem_barX' p).2 ⟨⟨t', ht'.1⟩, ht', rfl⟩, ?_⟩
    obtain ⟨z, hz, hzeq⟩ := hn
    have e : z = (⟨t, ht.1⟩ * ⟨t', ht'.1⟩ : ↥H)⁻¹ * x := Subtype.ext (by simpa using hzeq)
    have hmk : QuotientGroup.mk' (GLAPPrimeCore p ↥H) (⟨t, ht.1⟩ * ⟨t', ht'.1⟩ : ↥H) =
        QuotientGroup.mk' (GLAPPrimeCore p ↥H) x := by
      refine (QuotientGroup.eq).2 ?_
      rw [← e]
      exact hz
    rw [← hmk, map_mul]
  have hK : CFSG.IsComponent (barX p H L0) := (CFSG.isComponent_iff_open _).2 hL0H.2.2.1
  rcases CFSG.LocalCores.component_normal_subgroup hK hNT with hle | hc1
  · left
    exact bar_L0_le_of_le (L0_le_of_bar_le h133 h hL inf_le_left hTn hle)
  · rcases CFSG.LocalCores.component_normal_subgroup hK hNT' with hle' | hc2
    · right
      exact bar_L0_le_of_le (L0_le_of_bar_le h133 h hL inf_le_left hT'n hle')
    · exfalso
      have hc1' : ∀ k ∈ barX p H L0, ∀ a ∈ barX p H T, a * k = k * a := fun k hk a ha =>
        Subgroup.mem_centralizer_iff.1 ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc1) hk) a ha
      have hc2' : ∀ k ∈ barX p H L0, ∀ a ∈ barX p H T', a * k = k * a := fun k hk a ha =>
        Subgroup.mem_centralizer_iff.1 ((Subgroup.commutator_eq_bot_iff_le_centralizer.1 hc2) hk) a ha
      have hab : ∀ k₁ ∈ barX p H L0, ∀ k₂ ∈ barX p H L0, k₁ * k₂ = k₂ * k₁ := by
        intro k₁ hk₁ k₂ hk₂
        obtain ⟨a, ha, b, hb, rfl⟩ := hprod k₂ hk₂
        have h1 := hc1' k₁ hk₁ a ha
        have h2 := hc2' k₁ hk₁ b hb
        calc k₁ * (a * b) = (k₁ * a) * b := by group
          _ = (a * k₁) * b := by rw [h1]
          _ = a * (k₁ * b) := by group
          _ = a * (b * k₁) := by rw [h2]
          _ = (a * b) * k₁ := by group
      have hbot : ⁅barX p H L0, barX p H L0⁆ = ⊥ := by
        rw [eq_bot_iff]
        refine Subgroup.commutator_le.2 fun x hx y hy => ?_
        rw [Subgroup.mem_bot]
        exact commutatorElement_eq_one_iff_mul_comm.2 (hab x hx y hy)
      rw [barX_perfect_of_glaPComponent hL0H] at hbot
      exact isComponentOf_ne_bot' hL0H.2.2.1 hbot

theorem V1_le_of_L0_le (h : Cex1310 G m p B M E A D T R L0 d)
    {Z : Subgroup (↥M ⧸ GLAPPrimeCore p ↥M)}
    (hZ : barX p M (Istar p M D) ≤ Subgroup.normalizer (Z : Set (↥M ⧸ GLAPPrimeCore p ↥M)))
    (hΛ : barX p M L0 ≤ Z) : barX p M (L1of p M D L0) ≤ Z := by
  refine (barX_iSup_conj_le p (C := M) (Js := Istar p M D) (S := L0) (istar_le_M p M D)
    ((L0_le_istar h).trans (istar_le_M p M D))).trans ?_
  refine iSup₂_le fun y hy => ?_
  calc GLBConj y (barX p M L0) ≤ GLBConj y Z := gLBConj_mono y hΛ
    _ = Z := gLBConj_eq_of_mem_normalizer (hZ hy)

theorem orbit_of_cex (h133 : Lemma133Statement) (h : Cex1310 G m p B M E A D T R L0 d) :
    ∃ L : Subgroup G, GLAPComponent p (Istar p M D) L ∧
      barX p M (L1of p M D L0) = ⨆ i : Fin p, barX p M (GLBConj (d ^ (i : ℕ)) L) := by
  have hp := prime_of h
  obtain ⟨L, hL, hLV⟩ := exists_comp_le_V1 h133 h
  refine ⟨L, hL, le_antisymm ?_ (Worb_le_V1 h hLV)⟩
  rcases L0_support h133 h hL hLV with hW | hY
  · exact V1_le_of_L0_le h (V_le_normalizer_Worb h hL) hW
  · exfalso
    have hV1Y := V1_le_of_L0_le h (V_le_normalizer_Yorb h hL) hY
    have hWY : Worb p M D d L ≤ Yorb p M D L0 d L := (Worb_le_V1 h hLV).trans hV1Y
    have hWbot : Worb p M D d L = ⊥ := by
      rw [eq_bot_iff, ← Worb_inf_Yorb h133 h hL]
      exact le_inf le_rfl hWY
    have hLW : barX p M L ≤ Worb p M D d L := by
      have := le_iSup (fun i : Fin p => barX p M (GLBConj (d ^ (i : ℕ)) L)) ⟨0, hp.pos⟩
      simpa [gLBConj_one] using this
    rw [hWbot, le_bot_iff] at hLW
    exact isComponentOf_ne_bot' (Lemma1311.isComponent_barX_of_pComp hp hL) hLW


end Config



end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma1312b

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround

theorem lemma1312_of_inputs' (h133 : Lemma133Statement) : Lemma1312Statement := by
  intro G _ _ m p B M E A D T R L0 d h
  obtain ⟨L, hL, hV⟩ := Lemma1312b.orbit_of_cex h133 h
  exact Sec13g.lemma1312_of_inputs h (Lemma1312b.hint_holds h133 h hL hV)
    (Lemma1312b.hx_holds h133 h hL hV) (fun _ => Lemma1312b.hcB_holds h133 h hL hV)


end CFSG.LocalAnalysis.GLTheoremB.MovingAround

end
