module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResStab
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResLift
public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.CResChiefAbs
public import Mathlib.Algebra.Order.Ring.Star
public import Mathlib.Tactic.Polynomial.Basic

public section

namespace CFSG.EvenSporadicStandard.M24Std

open Subgroup
open scoped commutatorElement

@[expose] def ElemAbH1 : Prop :=
  ∀ {p r : ℕ} [Fact p.Prime], p ≠ 2 → ∀ {V : Type} [CommGroup V] [Finite V],
    (∀ v : V, v ^ p = 1) → Nat.card V = p ^ r → ∀ S : Subgroup (MulAut V),
    (∀ s ∈ S, s * s = 1) → (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) →
    Nat.card S ≤ 2 ^ r ∧ (Nat.card S = 2 ^ r → MulEquiv.inv V ∈ S)

@[expose] def ElemAbH2 : Prop :=
  ∀ {p r : ℕ} [Fact p.Prime], p ≠ 2 → ∀ {V : Type} [CommGroup V] [Finite V],
    (∀ v : V, v ^ p = 1) → Nat.card V = p ^ r → ∀ S : Subgroup (MulAut V),
    (∀ s ∈ S, s * s = 1) → (∀ s ∈ S, ∀ t ∈ S, s * t = t * s) → Nat.card S = 8 →
    (∀ s ∈ S, ∀ t ∈ S, s ≠ 1 → t ≠ 1 → ∃ g : MulAut V, g * s * g⁻¹ = t) → 7 ≤ r

structure ChiefData (E : Type) [Group E] (N0 : ℕ) : Prop where
  simple : ∀ N : Subgroup E, N.Normal → N = ⊥ ∨ N = ⊤
  center : ∀ e : E, (∀ x : E, x * e = e * x) → e = 1
  rank : ∃ m : ℕ, (∃ S₀ : Subgroup E, (∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a) ∧
      (∀ a ∈ S₀, a * a = 1) ∧ Nat.card S₀ = 2 ^ m) ∧
    ((∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * Nat.card E ∣ N0 → r ≤ m) ∨
      ((∃ S₈ : Subgroup E, (∀ a ∈ S₈, ∀ b ∈ S₈, a * b = b * a) ∧ (∀ a ∈ S₈, a * a = 1) ∧
          Nat.card S₈ = 8 ∧ ∀ s ∈ S₈, ∀ t ∈ S₈, s ≠ 1 → t ≠ 1 → ∃ g : E, g * s * g⁻¹ = t) ∧
        ∀ p r : ℕ, p.Prime → p ≠ 2 → p ^ r * Nat.card E ∣ N0 → r ≤ 6))

variable {U E : Type} [Group U] [Group E]

theorem derivedSeries_eq_top_of_perfect (hU : commutator U = ⊤) (n : ℕ) :
    derivedSeries U n = ⊤ := by
  induction n with
  | zero => rfl
  | succ n ih => rw [derivedSeries_succ, ih]; exact hU

theorem ker_le_of_nontrivial [Finite U] (hFT : OddSolv) (hU : commutator U = ⊤) (q : U →* E)
    (hq : Function.Surjective q) (hodd : Odd (Nat.card q.ker))
    (hE : ∀ N : Subgroup E, N.Normal → N = ⊥ ∨ N = ⊤) {G' : Type} [Group G'] (ρ : U →* G')
    (hρ : ∃ x, ρ x ≠ 1) : ρ.ker ≤ q.ker := by
  by_contra hnot
  have hKn : (ρ.ker.map q).Normal := Subgroup.Normal.map inferInstance q hq
  rcases hE _ hKn with hbot | htop
  · apply hnot
    intro k hk
    have : q k ∈ ρ.ker.map q := mem_map_of_mem q hk
    rw [hbot, mem_bot] at this
    exact this
  · obtain ⟨x, hx⟩ := hρ
    have hrange : ρ.range = q.ker.map ρ := by
      ext y
      constructor
      · rintro ⟨u, rfl⟩
        have hu : q u ∈ ρ.ker.map q := by rw [htop]; exact mem_top _
        obtain ⟨k, hk, hkq⟩ := hu
        have hk1 : ρ k = 1 := hk
        refine ⟨k⁻¹ * u, ?_, ?_⟩
        · show q (k⁻¹ * u) = 1
          rw [map_mul, map_inv, hkq, inv_mul_cancel]
        · rw [map_mul, map_inv, hk1, inv_one, one_mul]
      · rintro ⟨u, _, rfl⟩
        exact ⟨u, rfl⟩
    have hRodd : Odd (Nat.card ρ.range) := by
      rw [hrange]
      exact Odd.of_dvd_nat hodd (Subgroup.card_map_dvd _ _)
    have : Finite ρ.range :=
      Finite.of_surjective ρ.rangeRestrict (MonoidHom.rangeRestrict_surjective ρ)
    have hsolv : Group.IsSolvable ρ.range := hFT _ hRodd
    obtain ⟨n, hn⟩ := hsolv.solvable
    have h1 : derivedSeries ρ.range n = ⊤ := by
      rw [← map_derivedSeries_eq (f := ρ.rangeRestrict) (MonoidHom.rangeRestrict_surjective ρ) n,
        derivedSeries_eq_top_of_perfect hU n, ← MonoidHom.range_eq_map,
        MonoidHom.range_eq_top]
      exact MonoidHom.rangeRestrict_surjective ρ
    rw [hn] at h1
    have h2 : (⟨ρ x, ρ.mem_range.2 ⟨x, rfl⟩⟩ : ρ.range) = 1 := by
      have : (⟨ρ x, ρ.mem_range.2 ⟨x, rfl⟩⟩ : ρ.range) ∈ (⊥ : Subgroup ρ.range) := by
        rw [h1]; exact mem_top _
      exact mem_bot.1 this
    exact hx (congrArg Subtype.val h2)

theorem card_eq_of_injOn {G H : Type*} [Group G] [Group H] (f : G →* H) (S : Subgroup G)
    (hinj : ∀ s ∈ S, f s = 1 → s = 1) : Nat.card S = Nat.card (S.map f) := by
  have hinj' : Function.Injective (f.comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    intro s hs
    exact Subtype.ext (hinj s s.2 hs)
  have hrange : (f.comp S.subtype).range = S.map f := by
    ext y
    simp [MonoidHom.mem_range, mem_map]
  rw [← hrange]
  exact Nat.card_congr (MonoidHom.ofInjective hinj').toEquiv

theorem inv_mulAut_comm {V : Type*} [CommGroup V] (α : MulAut V) :
    α * MulEquiv.inv V = MulEquiv.inv V * α := by
  ext v
  simp

theorem false_of_rank_le [Finite U] (hH1 : ElemAbH1) {p r m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type} [CommGroup V] [Finite V] (hexp : ∀ v : V, v ^ p = 1)
    (hVcard : Nat.card V = p ^ r) (hVnt : Nontrivial V) (q : U →* E)
    (hq : Function.Surjective q) (hodd : Odd (Nat.card q.ker))
    (hcenter : ∀ e : E, (∀ x : E, x * e = e * x) → e = 1) (ρ : U →* MulAut V)
    (hker : ρ.ker ≤ q.ker) (S₀ : Subgroup E) (hab : ∀ a ∈ S₀, ∀ b ∈ S₀, a * b = b * a)
    (h2 : ∀ a ∈ S₀, a * a = 1) (hS₀ : Nat.card S₀ = 2 ^ m) (hrm : r ≤ m) : False := by
  obtain ⟨S, hSmap, hSinj, hSab, hS2⟩ := exists_lift_elemAb q hq hodd S₀ hab h2
  have hSρ : ∀ s ∈ S, ρ s = 1 → s = 1 := fun s hs h1 =>
    hSinj s hs (MonoidHom.mem_ker.1 (hker (MonoidHom.mem_ker.2 h1)))
  have hScard : Nat.card S = 2 ^ m := by
    rw [card_eq_of_injOn q S hSinj, hSmap, hS₀]
  set T : Subgroup (MulAut V) := S.map ρ with hT
  have hTcard : Nat.card T = 2 ^ m := by
    rw [← card_eq_of_injOn ρ S hSρ, hScard]
  have hT2 : ∀ t ∈ T, t * t = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hS2 a ha, map_one]
  have hTab : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hSab a ha b hb]
  obtain ⟨hle, hinv⟩ := hH1 hp2 hexp hVcard T hT2 hTab
  have hmr : m = r := by
    have : 2 ^ m ≤ 2 ^ r := hTcard ▸ hle
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 this
    omega
  obtain ⟨s, hs, hsρ⟩ := hinv (by rw [hTcard, hmr])
  have hcentral : ∀ x : U, x * s * x⁻¹ * s⁻¹ ∈ ρ.ker := by
    intro x
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hsρ]
    have := inv_mulAut_comm (ρ x)
    calc ρ x * MulEquiv.inv V * (ρ x)⁻¹ * (MulEquiv.inv V)⁻¹
        = (MulEquiv.inv V * ρ x) * (ρ x)⁻¹ * (MulEquiv.inv V)⁻¹ := by rw [← this]
      _ = 1 := by group
  have hqs : q s = 1 := by
    apply hcenter
    intro e
    obtain ⟨x, rfl⟩ := hq e
    have h1 := MonoidHom.mem_ker.1 (hker (hcentral x))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    have h3 : q x * q s * (q x)⁻¹ = q s := by
      have := mul_inv_eq_one.1 h1
      exact this
    calc q x * q s = q x * q s * (q x)⁻¹ * q x := by group
      _ = q s * q x := by rw [h3]
  have hs1 : s = 1 := hSinj s hs hqs
  rw [hs1, map_one] at hsρ
  have hp : p ∣ Nat.card V := by
    have : 0 < r := by
      by_contra h0
      have hr0 : r = 0 := by omega
      rw [hr0, pow_zero] at hVcard
      have := Finite.one_lt_card (α := V)
      omega
    rw [hVcard]
    exact dvd_pow_self p this.ne'
  obtain ⟨v, hv⟩ := exists_prime_orderOf_dvd_card' p hp
  have hvv : v⁻¹ = v := by
    have := congrArg (fun α : MulAut V => α v) hsρ
    simpa using this.symm
  have hv2 : v ^ 2 = 1 := by
    rw [sq]
    exact mul_eq_one_iff_eq_inv.2 hvv.symm
  have : orderOf v ∣ 2 := orderOf_dvd_of_pow_eq_one hv2
  rw [hv] at this
  exact hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out) Nat.prime_two).1 this)

theorem false_of_eight [Finite U] (hH2 : ElemAbH2) {p r : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type} [CommGroup V] [Finite V] (hexp : ∀ v : V, v ^ p = 1)
    (hVcard : Nat.card V = p ^ r) (q : U →* E) (hq : Function.Surjective q)
    (hodd : Odd (Nat.card q.ker)) (ρ : U →* MulAut V) (hker : ρ.ker ≤ q.ker)
    (S₈ : Subgroup E) (hab : ∀ a ∈ S₈, ∀ b ∈ S₈, a * b = b * a) (h2 : ∀ a ∈ S₈, a * a = 1)
    (h8 : Nat.card S₈ = 8)
    (hconj : ∀ s ∈ S₈, ∀ t ∈ S₈, s ≠ 1 → t ≠ 1 → ∃ g : E, g * s * g⁻¹ = t) (hr6 : r ≤ 6) :
    False := by
  obtain ⟨S, hSmap, hSinj, hSab, hS2⟩ := exists_lift_elemAb q hq hodd S₈ hab h2
  have hSρ : ∀ s ∈ S, ρ s = 1 → s = 1 := fun s hs h1 =>
    hSinj s hs (MonoidHom.mem_ker.1 (hker (MonoidHom.mem_ker.2 h1)))
  have hScard : Nat.card S = 8 := by
    rw [card_eq_of_injOn q S hSinj, hSmap, h8]
  set T : Subgroup (MulAut V) := S.map ρ with hT
  have hTcard : Nat.card T = 8 := by
    rw [← card_eq_of_injOn ρ S hSρ, hScard]
  have hT2 : ∀ t ∈ T, t * t = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, hS2 a ha, map_one]
  have hTab : ∀ s ∈ T, ∀ t ∈ T, s * t = t * s := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hSab a ha b hb]
  have hconjT : ∀ s ∈ T, ∀ t ∈ T, s ≠ 1 → t ≠ 1 → ∃ g : MulAut V, g * s * g⁻¹ = t := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ hρa hρb
    have ha1 : a ≠ 1 := fun h => hρa (by rw [h, map_one])
    have hb1 : b ≠ 1 := fun h => hρb (by rw [h, map_one])
    have hqa : q a ∈ S₈ := hSmap ▸ mem_map_of_mem q ha
    have hqb : q b ∈ S₈ := hSmap ▸ mem_map_of_mem q hb
    have hqa1 : q a ≠ 1 := fun h => ha1 (hSinj a ha h)
    have hqb1 : q b ≠ 1 := fun h => hb1 (hSinj b hb h)
    obtain ⟨g, hg⟩ := hconj (q a) hqa (q b) hqb hqa1 hqb1
    obtain ⟨y, rfl⟩ := hq g
    have hu : q (y * a * y⁻¹) = q b := by rw [map_mul, map_mul, map_inv]; exact hg
    have hu2 : (y * a * y⁻¹) * (y * a * y⁻¹) = 1 := by
      calc (y * a * y⁻¹) * (y * a * y⁻¹) = y * (a * a) * y⁻¹ := by group
        _ = 1 := by rw [hS2 a ha]; group
    obtain ⟨h', hh'⟩ := exists_conj_of_map_eq q hodd (t := b) (u := y * a * y⁻¹) (hS2 b hb) hu2
      hu.symm
    refine ⟨(ρ (y⁻¹ * h'))⁻¹, ?_⟩
    have ha' : a = (y⁻¹ * h') * b * (y⁻¹ * h')⁻¹ := by
      have : (y⁻¹ * h') * b * (y⁻¹ * h')⁻¹ = y⁻¹ * (h' * b * h'⁻¹) * y := by group
      rw [this, hh']
      group
    conv_lhs => rw [ha']
    simp only [map_mul, map_inv]
    group
  have := hH2 hp2 hexp hVcard T hT2 hTab hTcard hconjT
  omega

theorem chiefAct_trivial [Finite U] [Finite E] (hFT : OddSolv) (hH1 : ElemAbH1) (hH2 : ElemAbH2)
    (hU : commutator U = ⊤) (q : U →* E) (hq : Function.Surjective q)
    (hodd : Odd (Nat.card q.ker)) {N0 : ℕ} (hN0 : Nat.card U ∣ N0) (hE : ChiefData E N0)
    {B N : Subgroup U} [B.Normal] [N.Normal] (hBN : B ≤ N) (hne : B ≠ N) (hNO : N ≤ q.ker)
    (hchief : ∀ K : Subgroup U, K.Normal → B ≤ K → K ≤ N → K = B ∨ K = N) :
    ∀ x : U, chiefAct B N x = 1 := by
  by_contra hnt'
  have hnt : ∃ x : U, chiefAct B N x ≠ 1 := not_forall.1 hnt'
  have hNodd : Odd (Nat.card N) := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hNO)
  obtain ⟨p, r, hp, hp2, hWcard, hexp, hcomm⟩ := chief_elemAb hFT hBN hne hNodd hchief
  have : Fact p.Prime := ⟨hp⟩
  have hker := ker_le_of_nontrivial hFT hU q hq hodd hE.simple (chiefAct B N) hnt
  have hnt' : Nontrivial (chiefW B N) := by
    obtain ⟨n, hnN, hnB⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hBN hne)
    refine ⟨⟨⟨QuotientGroup.mk' B n, n, hnN, rfl⟩, 1, ?_⟩⟩
    intro h
    have h' : QuotientGroup.mk' B n = 1 := congrArg Subtype.val h
    exact hnB ((QuotientGroup.eq_one_iff n).1 h')
  have hUcard : Nat.card U = Nat.card E * Nat.card q.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup q.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective q hq).toEquiv]
  have hdvd : p ^ r * Nat.card E ∣ N0 := by
    have h1 : p ^ r ∣ Nat.card q.ker := by
      rw [← hWcard]
      exact (Subgroup.card_map_dvd N (QuotientGroup.mk' B)).trans
        (Subgroup.card_dvd_of_le hNO)
    have h2 : p ^ r * Nat.card E ∣ Nat.card U := by
      rw [hUcard, mul_comm (Nat.card E)]
      exact mul_dvd_mul_right h1 _
    exact h2.trans hN0
  let _ : CommGroup (chiefW B N) := { (inferInstance : Group (chiefW B N)) with mul_comm := hcomm }
  obtain ⟨m, ⟨S₀, hab, h2, hS₀⟩, hrank⟩ := hE.rank
  have hrm_of : r ≤ m → False := fun hrm =>
    false_of_rank_le hH1 hp2 hexp hWcard hnt' q hq hodd hE.center (chiefAct B N) hker S₀ hab h2
      hS₀ hrm
  rcases hrank with hA | ⟨⟨S₈, hab8, h28, h8, hconj⟩, h6⟩
  · exact hrm_of (hA p r hp hp2 hdvd)
  · by_cases hrm : r ≤ m
    · exact hrm_of hrm
    · exact false_of_eight hH2 hp2 hexp hWcard q hq hodd (chiefAct B N) hker S₈ hab8 h28 h8
        hconj (h6 p r hp hp2 hdvd)

theorem chiefTrivial_of_data [Finite U] [Finite E] (hFT : OddSolv) (hH1 : ElemAbH1)
    (hH2 : ElemAbH2) (hU : commutator U = ⊤) (q : U →* E) (hq : Function.Surjective q)
    (hodd : Odd (Nat.card q.ker)) {N0 : ℕ} (hN0 : Nat.card U ∣ N0) (hE : ChiefData E N0) :
    ChiefTrivial q.ker := by
  intro B N hB hN hBN hNO hchief
  by_cases hBeq : B = N
  · subst hBeq
    rw [Subgroup.commutator_le]
    intro n hn g _
    rw [commutatorElement_def]
    have := hB.conj_mem n hn g
    have h2 : g * n⁻¹ * g⁻¹ ∈ B := by
      have := hB.conj_mem n⁻¹ (inv_mem hn) g
      simpa [mul_assoc] using this
    have := mul_mem hn h2
    simpa [mul_assoc] using this
  · rw [Subgroup.commutator_le]
    intro n hn g _
    have hw := chiefAct_trivial hFT hH1 hH2 hU q hq hodd hN0 hE hBN hBeq hNO hchief g
    have h1 : ((chiefAct B N g (⟨QuotientGroup.mk' B n, n, hn, rfl⟩ : chiefW B N) :
        chiefW B N) : U ⧸ B) = QuotientGroup.mk' B n := by
      rw [hw]
      rfl
    rw [chiefAct_apply] at h1
    have hcomm' : QuotientGroup.mk' B g * QuotientGroup.mk' B n =
        QuotientGroup.mk' B n * QuotientGroup.mk' B g := by
      have := mul_inv_eq_iff_eq_mul.1 h1
      exact this
    have h2 : QuotientGroup.mk' B (n * g * n⁻¹ * g⁻¹) = 1 := by
      simp only [map_mul, map_inv]
      rw [← hcomm']
      group
    exact (QuotientGroup.eq_one_iff _).1 h2

end CFSG.EvenSporadicStandard.M24Std
