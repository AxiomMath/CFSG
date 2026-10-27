module

public import CFSG.LocalAnalysis.GLTheoremB.Prop95FixedDefs
public import CFSG.LocalAnalysis.GLTheoremB.Prop95NonAbDiag

public section

namespace CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb

open Subgroup CFSG.Open
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.FF531 (FFChevConclusion)

section Core

variable {Q : Type} [Group Q] [Finite Q] {ι : Type} {N : Subgroup Q} {S : ι → Subgroup Q}

theorem normalizerMonoidHom_coe (T : Subgroup Q) (n : Q) (hn : n ∈ Subgroup.normalizer (T : Set Q))
    (t : T) : (((T.normalizerMonoidHom ⟨n, hn⟩) t : T) : Q) = n * t * n⁻¹ := rfl

theorem normalizerMonoidHom_pow (T : Subgroup Q) (n : Q) (hn : n ∈ Subgroup.normalizer (T : Set Q))
    {m : ℕ} (hm : n ^ m = 1) : (T.normalizerMonoidHom ⟨n, hn⟩) ^ m = 1 := by
  rw [← map_pow]
  have : (⟨n, hn⟩ : ↥(Subgroup.normalizer (T : Set Q))) ^ m = 1 := Subtype.ext (by simpa using hm)
  rw [this, map_one]

theorem orderOf_normalizerMonoidHom (T : Subgroup Q) {p : ℕ} (hp : p.Prime) (n : Q)
    (hn : n ∈ Subgroup.normalizer (T : Set Q)) (hnp : n ^ p = 1) (hcen : ¬ ∀ t ∈ T, n * t = t * n) :
    orderOf (T.normalizerMonoidHom ⟨n, hn⟩) = p := by
  have hfp := normalizerMonoidHom_pow T n hn hnp
  rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one hfp) with h1 | h1
  · exfalso
    apply hcen
    intro t ht
    have h2 : T.normalizerMonoidHom ⟨n, hn⟩ = 1 := orderOf_eq_one_iff.1 h1
    have h3 := congrArg (fun a : MulAut T => ((a ⟨t, ht⟩ : T) : Q)) h2
    simp only [normalizerMonoidHom_coe, MulAut.one_apply] at h3
    calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [h3]
  · exact h1

theorem exists_y [Finite ι] (hF : IsFactorization N S) (hodd : FixedOddFact) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (i : ι) (hcat : IsCatalogGroup ↥(S i)) (hpS : ¬ p ∣ Nat.card ↥(S i)) {d : Q}
    (hd : d ^ p = 1) :
    ∃ y ∈ ⨆ j ∈ Set.range (fun k : ℕ => ((hF.actHom d) ^ k) i), S j,
      y ≠ 1 ∧ d * y = y * d ∧ Odd (orderOf y) := by
  haveI := hF.simple i
  obtain ⟨s, hs1, hsodd⟩ := exists_odd_orderOf (hF.nonab i)
  have hSO : S i ≤ ⨆ j ∈ Set.range (fun k : ℕ => ((hF.actHom d) ^ k) i), S j :=
    le_iSup₂_of_le i ⟨0, by simp⟩ le_rfl
  by_cases hmove : hF.actHom d i = i
  · have hdn : d ∈ Subgroup.normalizer (S i : Set Q) := hF.actHom_eq_iff.1 hmove
    by_cases hcen : ∀ t ∈ S i, d * t = t * d
    · refine ⟨(s : Q), hSO s.2, fun h => hs1 (Subtype.ext h), hcen s s.2, ?_⟩
      rw [Subgroup.orderOf_coe]
      exact hsodd
    · have hf := orderOf_normalizerMonoidHom (S i) hp d hdn hd hcen
      obtain ⟨y, hy, hy1, hyodd⟩ :=
        hodd ↥(S i) p hp hp2 inferInstance (hF.nonab i) hcat hpS _ hf
      refine ⟨(y : Q), hSO y.2, fun h => hy1 (Subtype.ext h), ?_, ?_⟩
      · have h2 : d * (y : Q) * d⁻¹ = (y : Q) := congrArg Subtype.val (show _ = _ from hy)
        calc d * (y : Q) = d * (y : Q) * d⁻¹ * d := by group
          _ = y * d := by rw [h2]
      · rw [Subgroup.orderOf_coe]
        exact hyodd
  · obtain ⟨Φ, hΦinj, hΦd, hΦmem, -⟩ := exists_diag hF hp hd hmove
    refine ⟨Φ s, hΦmem s, ?_, hΦd s, ?_⟩
    · intro h
      apply hs1
      apply hΦinj
      rw [map_one]
      exact h
    · rw [orderOf_injective Φ hΦinj s]
      exact hsodd

theorem normalizes_core [Finite ι] (hF : IsFactorization N S) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {d h : Q} (hd : d ^ p = 1) {e : ℕ} (hh : h ^ (2 ^ e) = 1) (hdh : d * h = h * d)
    (i : ι)
    (hkey : ∀ y ∈ N, d * y = y * d → ∃ k : ℕ, (h * y * h⁻¹ * y⁻¹) ^ (2 ^ k) = 1) {y : Q}
    (hy : y ∈ ⨆ j ∈ Set.range (fun k : ℕ => ((hF.actHom d) ^ k) i), S j) (hy1 : y ≠ 1)
    (hyd : d * y = y * d) (hyo : Odd (orderOf y)) :
    h ∈ Subgroup.normalizer (S i : Set Q) := by
  classical
  rw [← hF.actHom_eq_iff]
  set σ := hF.actHom d with hσdef
  set τ := hF.actHom h with hτdef
  have hσ : σ ^ p = 1 := by rw [hσdef, ← map_pow, hd, map_one]
  have hτ : τ ^ (2 ^ e) = 1 := by rw [hτdef, ← map_pow, hh, map_one]
  have hcomm : σ * τ = τ * σ := by rw [hσdef, hτdef, ← map_mul, ← map_mul, hdh]
  by_contra hne
  have hnot : ∀ m : ℕ, τ i ≠ (σ ^ m) i := fun m hm =>
    hne (perm_apply_eq_of_orbit hp hp2 hσ hτ hcomm ⟨m, hm⟩)
  set O : Set ι := Set.range (fun k : ℕ => (σ ^ k) i) with hO
  have hdisj : Disjoint O (τ '' O) := by
    rw [Set.disjoint_left]
    rintro j ⟨a, rfl⟩ ⟨_, ⟨b, rfl⟩, hb⟩
    apply hnot ((p - 1) * b + a)
    have e1 : (σ ^ b) (τ i) = (σ ^ a) i := by
      have := congrArg (fun f : Equiv.Perm ι => f i) (Commute.pow_left (hcomm : Commute σ τ) b).eq
      simp only [Equiv.Perm.mul_apply] at this
      exact this.trans hb
    have hpb : (p - 1) * b + b = p * b := by
      have := hp.one_lt
      calc (p - 1) * b + b = ((p - 1) + 1) * b := by ring
        _ = p * b := by congr 1; omega
    have h1 : (σ ^ ((p - 1) * b)) ((σ ^ b) (τ i)) = τ i := by
      rw [← Equiv.Perm.mul_apply, ← pow_add, hpb, pow_mul, hσ, one_pow]
      rfl
    have h2 : (σ ^ ((p - 1) * b)) ((σ ^ a) i) = (σ ^ ((p - 1) * b + a)) i := by
      rw [← Equiv.Perm.mul_apply, ← pow_add]
    rw [← h1, e1, h2]
  have hdj := hF.disjoint_biSup_biSup hdisj
  have hyN : y ∈ N := (iSup₂_le fun j _ => hF.le j) hy
  obtain ⟨k, hk⟩ := hkey y hyN hyd
  have hconj : ∀ x ∈ ⨆ j ∈ O, S j, h * x * h⁻¹ ∈ ⨆ j ∈ τ '' O, S j := by
    have : (⨆ j ∈ O, S j) ≤ (⨆ j ∈ τ '' O, S j).comap (MulAut.conj h).toMonoidHom := by
      refine iSup₂_le fun j hj x hx => ?_
      show h * x * h⁻¹ ∈ ⨆ j ∈ τ '' O, S j
      have hx' : h * x * h⁻¹ ∈ S (τ j) := by
        rw [hτdef, hF.S_actHom h j, mem_cj]
        simpa [mul_assoc] using hx
      exact Subgroup.mem_iSup_of_mem (τ j)
        (Subgroup.mem_iSup_of_mem (show τ j ∈ τ '' O from ⟨j, hj, rfl⟩) hx')
    exact fun x hx => this hx
  have h1 : h * y * h⁻¹ ∈ ⨆ j ∈ τ '' O, S j := hconj y hy
  have h2 : y⁻¹ ∈ ⨆ j ∈ O, S j := Subgroup.inv_mem _ hy
  have hc : Commute (h * y * h⁻¹) y⁻¹ := (hF.commute_biSup hdisj.symm h1 h2)
  have h3 : (h * y * h⁻¹) ^ (2 ^ k) * (y⁻¹) ^ (2 ^ k) = 1 := by
    rw [← hc.mul_pow]
    simpa [mul_assoc] using hk
  have h4 : y ^ (2 ^ k) = (h * y * h⁻¹) ^ (2 ^ k) := by
    have : (h * y * h⁻¹) ^ (2 ^ k) = ((y⁻¹) ^ (2 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left h3
    rw [this, inv_pow, inv_inv]
  have h5 : y ^ (2 ^ k) ∈ ⨆ j ∈ τ '' O, S j := by
    rw [h4]
    exact Subgroup.pow_mem _ h1 _
  have h6 : y ^ (2 ^ k) ∈ ⨆ j ∈ O, S j := Subgroup.pow_mem _ hy _
  have h7 : y ^ (2 ^ k) = 1 := by
    have := hdj.le_bot ⟨h6, h5⟩
    simpa using this
  have h8 : orderOf y = 1 :=
    (Nat.Coprime.pow_right k hyo.coprime_two_right).eq_one_of_dvd (orderOf_dvd_of_pow_eq_one h7)
  exact hy1 (orderOf_eq_one_iff.1 h8)


theorem normalizes [Finite ι] (hF : IsFactorization N S) (hodd : FixedOddFact) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (i : ι) (hcat : IsCatalogGroup ↥(S i))
    (hpS : ¬ p ∣ Nat.card ↥(S i)) {d : Q} (hd : d ^ p = 1) {H : Subgroup Q}
    (hH2 : IsPGroup 2 ↥H) (hHd : ∀ h ∈ H, d * h = h * d)
    (hHn : ∀ y : Q, d * y = y * d → ∀ h ∈ H, y * h * y⁻¹ ∈ H) :
    ∀ h ∈ H, h ∈ Subgroup.normalizer (S i : Set Q) := by
  intro h hh
  obtain ⟨e, he⟩ := hH2 ⟨h, hh⟩
  have hh' : h ^ (2 ^ e) = 1 := by simpa using congrArg Subtype.val he
  obtain ⟨y, hy, hy1, hyd, hyo⟩ := exists_y hF hodd hp hp2 i hcat hpS hd
  refine normalizes_core hF hp hp2 hd hh' (hHd h hh) i ?_ hy hy1 hyd hyo
  intro y' _ hy'd
  have hz : h * y' * h⁻¹ * y'⁻¹ ∈ H := by
    have := H.mul_mem hh (hHn y' hy'd h⁻¹ (H.inv_mem hh))
    simpa [mul_assoc] using this
  obtain ⟨k, hk⟩ := hH2 ⟨_, hz⟩
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem centralizes_of_diag (hF : IsFactorization N S) [Finite ι] (i : ι) {d : Q}
    {H : Subgroup Q} (hH2 : IsPGroup 2 ↥H) (hHd : ∀ h ∈ H, d * h = h * d)
    (hHn : ∀ y : Q, d * y = y * d → ∀ h ∈ H, y * h * y⁻¹ ∈ H)
    (hnorm : ∀ h ∈ H, h ∈ Subgroup.normalizer (S i : Set Q)) (Φ : ↥(S i) →* Q)
    (hΦinj : Function.Injective Φ) (hΦd : ∀ s, d * Φ s = Φ s * d)
    (hΦeq : ∀ g : Q, g * d = d * g → ∀ s s' : ↥(S i), (s' : Q) = g * s * g⁻¹ →
      g * Φ s * g⁻¹ = Φ s') :
    ∀ h ∈ H, ∀ s ∈ S i, h * s = s * h := by
  haveI := hF.simple i
  let U : Subgroup ↥(S i) := H.comap Φ
  have hUn : U.Normal := by
    refine ⟨fun u hu s => ?_⟩
    show Φ (s * u * s⁻¹) ∈ H
    rw [map_mul, map_mul, map_inv]
    exact hHn (Φ s) (hΦd s) (Φ u) hu
  have hUp : IsPGroup 2 U := hH2.comap_of_injective Φ hΦinj
  have hU1 : U = ⊥ := eq_bot_of_normal_isPGroup (hF.nonab i) U hUp
  intro h hh s hs
  have hs' : h * s * h⁻¹ ∈ S i := (Subgroup.mem_normalizer_iff.1 (hnorm h hh) s).1 hs
  have hc : (⟨h * s * h⁻¹, hs'⟩ : ↥(S i)) * ⟨s, hs⟩⁻¹ ∈ U := by
    show Φ _ ∈ H
    rw [map_mul, map_inv, ← hΦeq h (hHd h hh).symm ⟨s, hs⟩ ⟨h * s * h⁻¹, hs'⟩ rfl]
    have := H.mul_mem hh (hHn (Φ ⟨s, hs⟩) (hΦd _) h⁻¹ (H.inv_mem hh))
    simpa [mul_assoc] using this
  rw [hU1, Subgroup.mem_bot, mul_inv_eq_one] at hc
  have := congrArg Subtype.val hc
  simp only at this
  calc h * s = h * s * h⁻¹ * h := by group
    _ = s * h := by rw [this]

theorem centralizes [Finite ι] (hF : IsFactorization N S) (htwo : FixedTwoFacts) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (i : ι) (hcat : IsCatalogGroup ↥(S i))
    (hpS : ¬ p ∣ Nat.card ↥(S i)) (hFF : FFChevConclusion ↥(S i)) {d : Q} (hd : d ^ p = 1)
    {H : Subgroup Q} (hH2 : IsPGroup 2 ↥H) (hHd : ∀ h ∈ H, d * h = h * d)
    (hHn : ∀ y : Q, d * y = y * d → ∀ h ∈ H, y * h * y⁻¹ ∈ H)
    (hnorm : ∀ h ∈ H, h ∈ Subgroup.normalizer (S i : Set Q)) :
    ∀ h ∈ H, ∀ s ∈ S i, h * s = s * h := by
  haveI := hF.simple i
  by_cases hmove : hF.actHom d i = i
  · have hdn : d ∈ Subgroup.normalizer (S i : Set Q) := hF.actHom_eq_iff.1 hmove
    by_cases hcen : ∀ t ∈ S i, d * t = t * d
    · refine centralizes_of_diag hF i hH2 hHd hHn hnorm (S i).subtype (S i).subtype_injective
        (fun s => hcen s s.2) ?_
      intro g _ s s' hs'
      exact hs'.symm
    · have hf := orderOf_normalizerMonoidHom (S i) hp d hdn hd hcen
      obtain ⟨hC2, hCg⟩ := htwo ↥(S i) p hp hp2 inferInstance (hF.nonab i) hcat hpS hFF _ hf
      set f : MulAut ↥(S i) := (S i).normalizerMonoidHom ⟨d, hdn⟩ with hfdef
      have hcentC : ∀ h ∈ H, ∀ c ∈ signalizerFixedSubgroup f, h * (c : Q) = (c : Q) * h := by
        intro h hh c hc
        have hcd : d * (c : Q) = (c : Q) * d := by
          have h2 : d * (c : Q) * d⁻¹ = (c : Q) := congrArg Subtype.val (show f c = c from hc)
          calc d * (c : Q) = d * (c : Q) * d⁻¹ * d := by group
            _ = c * d := by rw [h2]
        let V : Subgroup ↥(signalizerFixedSubgroup f) :=
          H.comap ((S i).subtype.comp (signalizerFixedSubgroup f).subtype)
        have hVn : V.Normal := by
          refine ⟨fun v hv c' => ?_⟩
          show ((c' * v * c'⁻¹ : ↥(signalizerFixedSubgroup f)) : Q) ∈ H
          have hc'd : d * ((c' : ↥(S i)) : Q) = ((c' : ↥(S i)) : Q) * d := by
            have h2 : d * ((c' : ↥(S i)) : Q) * d⁻¹ = ((c' : ↥(S i)) : Q) :=
              congrArg Subtype.val (show f c' = c' from c'.2)
            calc d * ((c' : ↥(S i)) : Q) = d * ((c' : ↥(S i)) : Q) * d⁻¹ * d := by group
              _ = ((c' : ↥(S i)) : Q) * d := by rw [h2]
          have := hHn _ hc'd (((v : ↥(signalizerFixedSubgroup f)) : ↥(S i)) : Q) hv
          simpa [mul_assoc] using this
        have hVp : IsPGroup 2 V := hH2.comap_of_injective _
          ((S i).subtype_injective.comp (signalizerFixedSubgroup f).subtype_injective)
        have hVle : V ≤ CFSG.pCore 2 ↥(signalizerFixedSubgroup f) :=
          CFSG.LieType.BorelTits.le_pCore 2 hVn hVp
        rw [hC2] at hVle
        have hu : h * (c : Q) * h⁻¹ * (c : Q)⁻¹ = 1 := by
          have hS' : h * (c : Q) * h⁻¹ ∈ S i :=
            (Subgroup.mem_normalizer_iff.1 (hnorm h hh) c).1 c.2
          have hu1 : h * (c : Q) * h⁻¹ * (c : Q)⁻¹ ∈ S i :=
            (S i).mul_mem hS' ((S i).inv_mem c.2)
          have hu2 : h * (c : Q) * h⁻¹ * (c : Q)⁻¹ ∈ H := by
            have := H.mul_mem hh (hHn _ hcd h⁻¹ (H.inv_mem hh))
            simpa [mul_assoc] using this
          have hud : d * (h * (c : Q) * h⁻¹ * (c : Q)⁻¹) = (h * (c : Q) * h⁻¹ * (c : Q)⁻¹) * d := by
            have hhd : h * d = d * h := (hHd h hh).symm
            have hhd' : h⁻¹ * d = d * h⁻¹ := by
              calc h⁻¹ * d = h⁻¹ * d * h * h⁻¹ := by group
                _ = h⁻¹ * (d * h) * h⁻¹ := by rw [mul_assoc h⁻¹ d h]
                _ = h⁻¹ * (h * d) * h⁻¹ := by rw [hhd]
                _ = d * h⁻¹ := by group
            have hcd' : (c : Q)⁻¹ * d = d * (c : Q)⁻¹ := by
              calc (c : Q)⁻¹ * d = (c : Q)⁻¹ * d * (c : Q) * (c : Q)⁻¹ := by group
                _ = (c : Q)⁻¹ * (d * (c : Q)) * (c : Q)⁻¹ := by rw [mul_assoc (c : Q)⁻¹ d c]
                _ = (c : Q)⁻¹ * ((c : Q) * d) * (c : Q)⁻¹ := by rw [hcd]
                _ = d * (c : Q)⁻¹ := by group
            calc d * (h * (c : Q) * h⁻¹ * (c : Q)⁻¹)
                = (d * h) * (c : Q) * h⁻¹ * (c : Q)⁻¹ := by group
              _ = (h * d) * (c : Q) * h⁻¹ * (c : Q)⁻¹ := by rw [← hhd]
              _ = h * (d * (c : Q)) * h⁻¹ * (c : Q)⁻¹ := by group
              _ = h * ((c : Q) * d) * h⁻¹ * (c : Q)⁻¹ := by rw [hcd]
              _ = h * (c : Q) * (d * h⁻¹) * (c : Q)⁻¹ := by group
              _ = h * (c : Q) * (h⁻¹ * d) * (c : Q)⁻¹ := by rw [hhd']
              _ = h * (c : Q) * h⁻¹ * (d * (c : Q)⁻¹) := by group
              _ = h * (c : Q) * h⁻¹ * ((c : Q)⁻¹ * d) := by rw [hcd']
              _ = (h * (c : Q) * h⁻¹ * (c : Q)⁻¹) * d := by group
          let u : ↥(S i) := ⟨_, hu1⟩
          have hu' : u ∈ signalizerFixedSubgroup f := by
            show f u = u
            apply Subtype.ext
            rw [hfdef, normalizerMonoidHom_coe]
            calc d * (u : Q) * d⁻¹ = (u : Q) * d * d⁻¹ := by rw [hud]
              _ = u := by group
          have hmemV : (⟨u, hu'⟩ : ↥(signalizerFixedSubgroup f)) ∈ V := hu2
          have := Subgroup.mem_bot.1 (hVle hmemV)
          exact congrArg (fun x : ↥(signalizerFixedSubgroup f) => ((x : ↥(S i)) : Q)) this
        calc h * (c : Q) = h * (c : Q) * h⁻¹ * (c : Q)⁻¹ * (c : Q) * h := by group
          _ = (c : Q) * h := by rw [hu]; group
      intro h hh s hs
      obtain ⟨e, he⟩ := hH2 ⟨h, hh⟩
      have hh' : h ^ (2 ^ e) = 1 := by simpa using congrArg Subtype.val he
      set g : MulAut ↥(S i) := (S i).normalizerMonoidHom ⟨h, hnorm h hh⟩ with hgdef
      have hg2 : IsPGroup 2 (Subgroup.zpowers g) := by
        have hge : g ^ (2 ^ e) = 1 := normalizerMonoidHom_pow (S i) h (hnorm h hh) hh'
        obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hge)
        exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
      have hgfix : ∀ x ∈ signalizerFixedSubgroup f, g x = x := by
        intro x hx
        apply Subtype.ext
        rw [hgdef, normalizerMonoidHom_coe]
        have := hcentC h hh x hx
        calc h * (x : Q) * h⁻¹ = (x : Q) * h * h⁻¹ := by rw [this]
          _ = x := by group
      have hg1 : g = 1 := hCg g hg2 hgfix
      have := congrArg (fun a : MulAut ↥(S i) => ((a ⟨s, hs⟩ : ↥(S i)) : Q)) hg1
      simp only [hgdef, normalizerMonoidHom_coe, MulAut.one_apply] at this
      calc h * s = h * s * h⁻¹ * h := by group
        _ = s * h := by rw [this]
  · obtain ⟨Φ, hΦinj, hΦd, -, hΦeq⟩ := exists_diag hF hp hd hmove
    exact centralizes_of_diag hF i hH2 hHd hHn hnorm Φ hΦinj hΦd hΦeq

end Core

end CFSG.LocalAnalysis.GLTheoremB.Prop95Parts.NonAb
