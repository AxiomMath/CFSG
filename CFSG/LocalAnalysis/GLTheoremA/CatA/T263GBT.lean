module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263GCase
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021FixCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021FixMax
public import CFSG.LocalAnalysis.GLTheoremA.CatA.D4TCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T2021RankHolds
public import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactSeitzOutside

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.I2015 CFSG.LocalAnalysis.GLTheoremA.T2021

section Certs


theorem t263_fixFact {H : Type} [Group H] [Finite H] {p : ℕ} {𝔅 : Type} [Group 𝔅] [Finite 𝔅]
    (ψ : 𝔅 →* MulAut H) {T : Subgroup H} (hp : p.Prime) (hp2 : p ≠ 2)
    (hchev : IsChevSimple 2 (psimpleOf p H)) (hperf : commutator (ppQuot p H) = ⊤)
    (hexp : ∀ g : 𝔅, g ^ p = 1) (hT2 : IsPGroup 2 T) (hTinv : ∀ g : 𝔅, ∀ t ∈ T, ψ g t ∈ T)
    (hTO : ¬ T ≤ GLAPPrimeCore p H)
    (hTmax : ∀ T' : Subgroup H, IsPGroup 2 T' → (∀ g : 𝔅, ∀ t ∈ T', ψ g t ∈ T') → T ≤ T' → T' = T)
    (g : 𝔅) (hg : ∀ t ∈ T, ψ g t * t⁻¹ ∈ GLAPPrimeCore p H) : TrivAut p H (ψ g) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := GLAPPrimeCore p H with hN
  let ψQ : 𝔅 →* MulAut (ppQuot p H) := (MulAut.mapQuotient N).comp ψ
  have hψQ : ∀ (g : 𝔅) (l : H), ψQ g (QuotientGroup.mk l) = QuotientGroup.mk (ψ g l) :=
    fun g l => MulAut.mapQuotient_mk N (ψ g) l
  set Z := Subgroup.center (ppQuot p H) with hZ
  let ψS : 𝔅 →* MulAut (psimpleOf p H) := (MulAut.mapQuotient Z).comp ψQ
  have hψS : ∀ (g : 𝔅) (x : ppQuot p H), ψS g (QuotientGroup.mk x) = QuotientGroup.mk (ψQ g x) :=
    fun g x => MulAut.mapQuotient_mk Z (ψQ g) x
  have h𝔅 : IsPGroup p 𝔅 := fun g => ⟨1, by rw [pow_one]; exact hexp g⟩
  have hs : IsSimpleGroup (psimpleOf p H) :=
    CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.isSimpleGroup_of_isChevSimple_two hchev
  have hna : ∃ a b : psimpleOf p H, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    have htop : commutator (psimpleOf p H) = ⊤ := by
      have h1 := Subgroup.map_commutator (⊤ : Subgroup (ppQuot p H)) ⊤ (QuotientGroup.mk' Z)
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective Z)] at h1
      rw [commutator_def, ← h1, ← commutator_def, hperf, Subgroup.map_top_of_surjective _
        (QuotientGroup.mk'_surjective Z)]
    have hbot : commutator (psimpleOf p H) = ⊥ := by
      rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro x _ y _
      exact hc y x
    have h1 : (⊤ : Subgroup (psimpleOf p H)) = ⊥ := htop.symm.trans hbot
    obtain ⟨a, b, hab⟩ := exists_pair_ne (psimpleOf p H)
    have ha : a = 1 := by
      have : a ∈ (⊤ : Subgroup (psimpleOf p H)) := trivial
      rw [h1, Subgroup.mem_bot] at this
      exact this
    have hb : b = 1 := by
      have : b ∈ (⊤ : Subgroup (psimpleOf p H)) := trivial
      rw [h1, Subgroup.mem_bot] at this
      exact this
    exact hab (ha.trans hb.symm)
  set Tb : Subgroup (psimpleOf p H) := (T.map (QuotientGroup.mk' N)).map (QuotientGroup.mk' Z) with hTb
  have hTb2 : IsPGroup 2 Tb := (hT2.map _).map _
  have hZodd : Odd (Nat.card Z) := t2021Fix_odd_center hp hp2
  have hTb1 : Tb ≠ ⊥ := by
    intro hbot
    apply hTO
    intro t ht
    have hq : (QuotientGroup.mk t : ppQuot p H) ∈ Z := by
      have h1 : QuotientGroup.mk' Z (QuotientGroup.mk' N t) ∈ Tb := ⟨_, ⟨t, ht, rfl⟩, rfl⟩
      rw [hbot, Subgroup.mem_bot] at h1
      exact (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨k, hk⟩ := (hT2.map (QuotientGroup.mk' N)) ⟨_, ⟨t, ht, rfl⟩⟩
    have hk' : (QuotientGroup.mk t : ppQuot p H) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hord : orderOf (⟨_, hq⟩ : Z) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext hk')
    have hodd : Odd (orderOf (⟨_, hq⟩ : Z)) := hZodd.of_dvd_nat (orderOf_dvd_natCard _)
    have h1 : orderOf (⟨_, hq⟩ : Z) = 1 := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
      rcases Nat.eq_zero_or_pos j with h0 | h0
      · rw [hj, h0, pow_zero]
      · exfalso
        rw [hj] at hodd
        exact (Nat.not_even_iff_odd.2 hodd) (Nat.even_pow.2 ⟨even_two, h0.ne'⟩)
    have h2 : (QuotientGroup.mk t : ppQuot p H) = 1 :=
      congrArg Subtype.val (orderOf_eq_one_iff.1 h1)
    exact (QuotientGroup.eq_one_iff t).1 h2
  have hrad := t2021Fix_radical hp hp2 ψ ψQ hψQ ψS hψS h𝔅 hT2 hTinv hTmax
  have hgT : ∀ x ∈ Tb, ψS g x = x := by
    rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
    simp only [QuotientGroup.mk'_apply]
    rw [hψS, hψQ]
    congr 1
    exact QuotientGroup.eq_iff_div_mem.2 (by rw [div_eq_mul_inv]; exact hg t ht)
  have hgp : ψS g ^ p = 1 := by rw [← map_pow, hexp, map_one]
  have hcore : ψS g = 1 := t2021Fix_core hs hna hchev hp hp2 hTb2 hTb1 hrad hgp hgT
  exact t2021Fix_trivAut hperf (ψ g) (ψQ g) (hψQ g) hcore

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem t263_bt_of_max {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S B T : Subgroup Ω} (hSn : S.Normal)
    (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hSc : IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S)) (hBel : CFSG.Open.IsElemAbelian p B)
    (hT2 : IsPGroup 2 T) (hTS : T ≤ S) (hTne : T ≠ ⊥) (hBT : B ≤ Subgroup.normalizer (T : Set Ω))
    (hmax : ∀ T' : Subgroup Ω, T' ≤ S → IsPGroup 2 T' → B ≤ Subgroup.normalizer (T' : Set Ω) → T ≤ T' →
      T' = T) :
    B ⊓ Subgroup.centralizer (T : Set Ω) ≤ Subgroup.centralizer (S : Set Ω) := by
  classical
  have hAN : B ≤ Subgroup.normalizer (S : Set Ω) := by
    rw [Subgroup.normalizer_eq_top_iff.2 hSn]
    exact le_top
  let ψ : ↥B →* MulAut ↥S := (CFSG.LocalAnalysis.GLTheoremA.D4T.conjHom S).comp (Subgroup.inclusion hAN)
  have hψ : ∀ (g : ↥B) (x : ↥S), ((ψ g x : ↥S) : Ω) = (g : Ω) * (x : Ω) * (g : Ω)⁻¹ := fun g x => rfl
  let eS : PQuot p S ≃* ↥S := (QuotientGroup.quotientMulEquivOfEq hSp).trans QuotientGroup.quotientBot
  have hq : CFSG.Open.IsQuasisimple (PQuot p S) := hSq.of_mulEquiv eS
  have e₆ : PSimple p S ≃* ↥S ⧸ Subgroup.center ↥S :=
    QuotientGroup.congr _ _ eS (Subgroup.map_center_eq eS)
  have hchev : IsChevSimple 2 (psimpleOf p ↥S) := by
    unfold IsChevSimple at hSc ⊢
    rcases hSc with h | h
    · exact Or.inl ((catalogIs_congr e₆).2 h)
    · exact Or.inr ((catalogIs_congr e₆).2 h)
  set T₀ : Subgroup ↥S := T.subgroupOf S with hT₀
  have hT₀mem : ∀ x : ↥S, x ∈ T₀ ↔ (x : Ω) ∈ T := fun x => Subgroup.mem_subgroupOf
  have hT₀2 : IsPGroup 2 T₀ := hT2.of_equiv (Subgroup.subgroupOfEquivOfLe hTS).symm
  have hT₀inv : ∀ g : ↥B, ∀ t ∈ T₀, ψ g t ∈ T₀ := by
    intro g t ht
    rw [hT₀mem, hψ]
    exact (Subgroup.mem_normalizer_iff.1 (hBT g.2) (t : Ω)).1 ((hT₀mem t).1 ht)
  have hT₀O : ¬ T₀ ≤ GLAPPrimeCore p ↥S := by
    intro h
    rw [hSp] at h
    apply hTne
    have hbot : T₀ = ⊥ := le_bot_iff.1 h
    rw [← Subgroup.map_subgroupOf_eq_of_le hTS, ← hT₀, hbot, Subgroup.map_bot]
  have hT₀max : ∀ T' : Subgroup ↥S, IsPGroup 2 T' → (∀ g : ↥B, ∀ t ∈ T', ψ g t ∈ T') → T₀ ≤ T' →
      T' = T₀ := by
    intro T' hT'2 hT'inv hT₀T'
    have hmem'' : ∀ h : Ω, h ∈ T'.map S.subtype ↔ ∃ y : ↥S, y ∈ T' ∧ (y : Ω) = h := fun h => by
      simp [Subgroup.mem_map]
    have hBN'' : B ≤ Subgroup.normalizer ((T'.map S.subtype : Subgroup Ω) : Set Ω) := by
      intro b hb
      rw [Subgroup.mem_normalizer_iff]
      intro h
      constructor
      · intro hh
        obtain ⟨y, hy, rfl⟩ := (hmem'' h).1 hh
        exact (hmem'' _).2 ⟨ψ ⟨b, hb⟩ y, hT'inv ⟨b, hb⟩ y hy, hψ ⟨b, hb⟩ y⟩
      · intro hh
        obtain ⟨y, hy, hyh⟩ := (hmem'' _).1 hh
        have hb' : b⁻¹ ∈ B := inv_mem hb
        refine (hmem'' h).2 ⟨ψ ⟨b⁻¹, hb'⟩ y, hT'inv ⟨b⁻¹, hb'⟩ y hy, ?_⟩
        rw [hψ]
        simp only [hyh]
        group
    have hT''T : T ≤ T'.map S.subtype := by
      intro x hx
      exact (hmem'' x).2 ⟨⟨x, hTS hx⟩, hT₀T' ((hT₀mem _).2 hx), rfl⟩
    have hEq := hmax (T'.map S.subtype) (Subgroup.map_subtype_le T') (hT'2.map _) hBN'' hT''T
    ext x
    rw [hT₀mem, ← hEq, hmem'']
    constructor
    · intro hx
      exact ⟨x, hx, rfl⟩
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      exact this ▸ hy
  have hexp : ∀ g : ↥B, g ^ p = 1 := fun g => Subtype.ext (hBel.2 g g.2)
  intro g hg
  have hgB : g ∈ B := hg.1
  have hgT : g ∈ Subgroup.centralizer (T : Set Ω) := hg.2
  have key := t263_fixFact ψ hp hp2 hchev hq.1 hexp hT₀2 hT₀inv hT₀O hT₀max ⟨g, hgB⟩ (by
    intro t ht
    have hc : g * (t : Ω) = (t : Ω) * g := (Subgroup.mem_centralizer_iff.1 hgT (t : Ω) ((hT₀mem t).1 ht)).symm
    rw [hSp]
    refine Subgroup.mem_bot.2 (Subtype.ext ?_)
    rw [Subgroup.coe_mul, hψ, Subgroup.coe_inv, hc]
    simp)
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h1 := key ⟨y, hy⟩
  rw [hSp, Subgroup.mem_bot] at h1
  have h2 := congrArg Subtype.val h1
  rw [Subgroup.coe_mul, hψ, Subgroup.coe_inv] at h2
  simp only [OneMemClass.coe_one] at h2
  have h3 : g * y * g⁻¹ = y := by
    have := h2
    calc g * y * g⁻¹ = g * y * g⁻¹ * y⁻¹ * y := by group
      _ = y := by rw [this, one_mul]
  calc y * g = (g * y * g⁻¹) * g := by rw [h3]
    _ = g * y := by group


theorem t263BT_holds (Q : TauCeti.CFSGIndex → Prop) : T263BT Q := by
  intro p hp hp2 Ω _ _ S B hSn hSq hSp hSc _ hBel hT
  classical
  obtain ⟨T₀, hT₀ne, hT₀2, hT₀S, hBT₀⟩ := hT
  obtain ⟨T, hT₀T, hTS, hT2, hBT, hmax⟩ : ∃ T : Subgroup Ω, T₀ ≤ T ∧ T ≤ S ∧ IsPGroup 2 T ∧
      B ≤ Subgroup.normalizer (T : Set Ω) ∧ ∀ T' : Subgroup Ω, T' ≤ S → IsPGroup 2 T' →
        B ≤ Subgroup.normalizer (T' : Set Ω) → T ≤ T' → T' = T := by
    let P : Set (Subgroup Ω) := {X | T₀ ≤ X ∧ X ≤ S ∧ IsPGroup 2 X ∧ B ≤ Subgroup.normalizer (X : Set Ω)}
    have hPne : P.Nonempty := ⟨T₀, le_rfl, hT₀S, hT₀2, hBT₀⟩
    obtain ⟨X, hXP, hXmax⟩ := Set.Finite.exists_maximalFor (fun X : Subgroup Ω => Nat.card ↥X) P
      (Set.toFinite P) hPne
    refine ⟨X, hXP.1, hXP.2.1, hXP.2.2.1, hXP.2.2.2, fun T' hT'S hT'2 hBT' hXT' => ?_⟩
    have hT'P : T' ∈ P := ⟨hXP.1.trans hXT', hT'S, hT'2, hBT'⟩
    have hle : Nat.card ↥X ≤ Nat.card ↥T' := Subgroup.card_le_of_le hXT'
    exact (Subgroup.eq_of_le_of_card_ge hXT' (hXmax hT'P hle)).symm
  have hTne : T ≠ ⊥ := fun h => hT₀ne (le_bot_iff.1 (h ▸ hT₀T))
  exact ⟨T, hTne, hT2, hTS, hBT, t263_bt_of_max hp hp2 hSn hSq hSp hSc hBel hT2 hTS hTne hBT hmax⟩

end Certs

end CFSG.LocalAnalysis.GLTheoremA.T263

end
