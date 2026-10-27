module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieTools
import CFSG.LocalAnalysis.SectionRank.DerivedQuotient
import CFSG.LocalAnalysis.PreuniquenessRankFour.Nongeneration

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure

open CFSG.Open

structure SylowTorusIrr (G : Type*) [Group G] (p m : ℕ) : Prop where
  exists_torus : ∃ T E : Subgroup G, IsMulCommutative T ∧
    (∀ P : Subgroup G, IsPGroup p P → ∃ g : G, P ≤ T.map (MulAut.conj g).toMonoidHom) ∧
    E ≤ T ∧ (∀ x ∈ T, x ^ p = 1 → x ∈ E) ∧ IsElemAbelian p E ∧ Nat.card E = p ^ m ∧
    ∀ V : Subgroup G, V ≤ E → V ≠ ⊥ →
      (∀ n ∈ Subgroup.normalizer (T : Set G), V.map (MulAut.conj n).toMonoidHom = V) → V = E

section Torus

variable {G : Type} [Group G] [Finite G] {p m : ℕ}

theorem SylowTorusIrr.irreducibleOnOmega1 [Fact p.Prime] (h : SylowTorusIrr G p m)
    (P : Sylow p G) : IrreducibleOnOmega1 p (P : Subgroup G) := by
  obtain ⟨T, E, hTab, hconj, hET, hE, hEel, hcard, hirr⟩ := h.exists_torus
  obtain ⟨g, hg⟩ := hconj (P : Subgroup G) P.isPGroup'
  have hPT : ∀ x ∈ (P : Subgroup G), g⁻¹ * x * g ∈ T := by
    intro x hx
    obtain ⟨t, ht, hte⟩ := hg hx
    have : g⁻¹ * x * g = t := by
      rw [← hte]
      simp [MulAut.conj_apply, mul_assoc]
    rw [this]
    exact ht
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := fun x hx y hy => setLike_mul_comm hx hy
  have hPmax : ∀ y : G, g⁻¹ * y * g ∈ T → (∃ k : ℕ, y ^ p ^ k = 1) → y ∈ (P : Subgroup G) := by
    intro y hyT ⟨k, hk⟩
    have hycomm : ∀ x ∈ (P : Subgroup G), x * y = y * x := by
      intro x hx
      have h1 := hTcomm _ (hPT x hx) _ hyT
      calc x * y = g * (g⁻¹ * x * g) * (g⁻¹ * y * g) * g⁻¹ := by group
        _ = g * (g⁻¹ * y * g) * (g⁻¹ * x * g) * g⁻¹ := by rw [mul_assoc g, h1, ← mul_assoc g]
        _ = y * x := by group
    have hz : IsPGroup p (Subgroup.zpowers y) := by
      refine IsPGroup.of_card_dvd_pow (n := k) ?_
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk
    have hnorm : (P : Subgroup G) ≤ Subgroup.normalizer
        ((Subgroup.zpowers y : Subgroup G) : Set G) := by
      intro x hx
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro z hz'
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz'
      exact ((Commute.zpow_right (show Commute x y from hycomm x hx) i).eq).symm
    have hQ : IsPGroup p ((P : Subgroup G) ⊔ Subgroup.zpowers y : Subgroup G) :=
      P.isPGroup'.to_sup_of_normal_right' hz hnorm
    obtain ⟨S, hS⟩ := hQ.exists_le_sylow
    have hPS : (P : Subgroup G) ≤ S := le_trans le_sup_left hS
    have hcardS : Nat.card (S : Subgroup G) ≤ Nat.card (P : Subgroup G) := by
      rw [S.card_eq_multiplicity, P.card_eq_multiplicity]
    have hPeq : (P : Subgroup G) = S := Subgroup.eq_of_le_of_card_ge hPS hcardS
    rw [hPeq]
    exact hS (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  have hconj_mem : ∀ n' ∈ Subgroup.normalizer (T : Set G), ∀ x ∈ (P : Subgroup G),
      (g * n' * g⁻¹) * x * (g * n' * g⁻¹)⁻¹ ∈ (P : Subgroup G) := by
    intro n' hn' x hx
    apply hPmax
    · have h1 := (Subgroup.mem_normalizer_iff.1 hn' (g⁻¹ * x * g)).1 (hPT x hx)
      have e : g⁻¹ * ((g * n' * g⁻¹) * x * (g * n' * g⁻¹)⁻¹) * g = n' * (g⁻¹ * x * g) * n'⁻¹ := by
        group
      rw [e]
      exact h1
    · obtain ⟨k, hk⟩ := P.isPGroup' ⟨x, hx⟩
      refine ⟨k, ?_⟩
      have hxk : x ^ p ^ k = 1 := congrArg Subtype.val hk
      rw [conj_pow, hxk]
      simp
  have hNP : ∀ n' ∈ Subgroup.normalizer (T : Set G),
      g * n' * g⁻¹ ∈ Subgroup.normalizer ((P : Subgroup G) : Set G) := by
    intro n' hn'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => hconj_mem n' hn' x hx
    · intro hx
      have := hconj_mem n'⁻¹ ((Subgroup.normalizer (T : Set G)).inv_mem hn') _ hx
      have e : (g * n'⁻¹ * g⁻¹) * ((g * n' * g⁻¹) * x * (g * n' * g⁻¹)⁻¹) *
          (g * n'⁻¹ * g⁻¹)⁻¹ = x := by group
      rwa [e] at this
  intro V hVP hVexp hVN
  set V' : Subgroup G := V.comap (MulAut.conj g).toMonoidHom with hV'
  have hV'mem : ∀ y, y ∈ V' ↔ g * y * g⁻¹ ∈ V := fun y => by
    simp [hV', Subgroup.mem_comap, MulAut.conj_apply]
  have hV'E : V' ≤ E := by
    intro y hy
    rw [hV'mem] at hy
    have hyT : y ∈ T := by
      have := hPT _ (hVP hy)
      simpa [mul_assoc] using this
    refine hE y hyT ?_
    have h1 := hVexp _ hy
    rw [conj_pow] at h1
    simpa using h1
  have hclaim : ∀ n ∈ Subgroup.normalizer (T : Set G), ∀ y ∈ V', n * y * n⁻¹ ∈ V' := by
    intro n hn y hy
    rw [hV'mem] at hy ⊢
    have hν := hVN _ (hNP n hn)
    have e : g * (n * y * n⁻¹) * g⁻¹ = (g * n * g⁻¹) * (g * y * g⁻¹) * (g * n * g⁻¹)⁻¹ := by
      group
    rw [e, ← hν]
    exact ⟨_, hy, rfl⟩
  have hinv : ∀ n ∈ Subgroup.normalizer (T : Set G),
      V'.map (MulAut.conj n).toMonoidHom = V' := by
    intro n hn
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [MulAut.conj_apply] using hclaim n hn y hy
    · intro hx
      refine ⟨n⁻¹ * x * n, ?_, by show n * (n⁻¹ * x * n) * n⁻¹ = x; group⟩
      have := hclaim n⁻¹ ((Subgroup.normalizer (T : Set G)).inv_mem hn) x hx
      simpa using this
  by_cases hVbot : V = ⊥
  · exact Or.inl hVbot
  · right
    have hV'bot : V' ≠ ⊥ := by
      intro h0
      apply hVbot
      refine (Subgroup.eq_bot_iff_forall V).2 fun v hv => ?_
      have hv' : g⁻¹ * v * g ∈ V' := by
        rw [hV'mem]
        simpa [mul_assoc] using hv
      rw [h0, Subgroup.mem_bot] at hv'
      have e : v = g * (g⁻¹ * v * g) * g⁻¹ := by group
      rw [e, hv']
      simp
    have hV'eq : V' = E := hirr V' hV'E hV'bot hinv
    intro x hx hxp
    have hxT := hPT x hx
    have hxE : g⁻¹ * x * g ∈ E := by
      refine hE _ hxT ?_
      rw [show g⁻¹ * x * g = g⁻¹ * x * g⁻¹⁻¹ by simp, conj_pow, hxp]
      simp
    rw [← hV'eq, hV'mem] at hxE
    simpa [mul_assoc] using hxE

theorem SylowTorusIrr.normalizerMovesLines [Fact p.Prime] (h : SylowTorusIrr G p m)
    (P : Sylow p G) (hrank : 2 ≤ CFSG.Open.pRank p (P : Subgroup G)) :
    NormalizerMovesLines p (P : Subgroup G) :=
  NormalizerMovesLines.of_irreducibleOnOmega1 hrank (h.irreducibleOnOmega1 P)

theorem WCOn.of_sylowTorusIrr [Fact p.Prime] (h : SylowTorusIrr G p m) : WCOn p G := by
  obtain ⟨P₀⟩ : Nonempty (Sylow p G) := inferInstance
  exact WCOn.of_normalizerMovesLines P₀ fun _ hrank => h.normalizerMovesLines P₀ hrank

end Torus

section Transitive

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem normalizerMovesLines_of_transitive [Fact p.Prime] {P : Subgroup K}
    (hrank : 2 ≤ CFSG.Open.pRank p P)
    (htrans : ∀ x ∈ P, ∀ y ∈ P, x ≠ 1 → y ≠ 1 → x ^ p = 1 → y ^ p = 1 →
      ∃ n ∈ Subgroup.normalizer (P : Set K), n * x * n⁻¹ = y) :
    NormalizerMovesLines p P := by
  intro A hAP hA
  by_contra hcon
  push Not at hcon
  have hconjA : ∀ n ∈ Subgroup.normalizer (P : Set K), ∀ y ∈ A, n * y * n⁻¹ ∈ A := by
    intro n hn y hy
    rw [← hcon n hn]
    exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
  have hexp : ∀ y ∈ A, y ^ p = 1 := by
    intro y hy
    have := pow_card_eq_one' (G := A) (x := ⟨y, hy⟩)
    rw [hA] at this
    exact congrArg Subtype.val this
  obtain ⟨x, hxA, hx1⟩ : ∃ x ∈ A, x ≠ 1 := by
    by_contra h
    push Not at h
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [this, Subgroup.card_bot] at hA
    exact (Fact.out : p.Prime).one_lt.ne hA
  obtain ⟨E, hEP, hE, hEcard⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank
    (p := p) (H := P) (k := 2) hrank
  obtain ⟨y, hyE, hyA⟩ : ∃ y ∈ E, y ∉ A := by
    by_contra h
    push Not at h
    have h1 : Nat.card E ≤ Nat.card A := Subgroup.card_le_of_le fun z hz => h z hz
    rw [hEcard, hA] at h1
    have hp2 := (Fact.out : p.Prime).two_le
    nlinarith
  have hy1 : y ≠ 1 := fun h => hyA (h ▸ A.one_mem)
  obtain ⟨n, hn, hnxy⟩ := htrans x (hAP hxA) y (hEP hyE) hx1 hy1 (hexp x hxA) (hE.2 y hyE)
  exact hyA (hnxy ▸ hconjA n hn x hxA)

end Transitive

section Burnside

variable {K : Type} [Group K] [Finite K] {p : ℕ}

theorem normalizerMovesLines_of_wcOn [Fact p.Prime] (hWC : WCOn p K) (P : Sylow p K)
    (hab : IsMulCommutative (P : Subgroup K)) (hrank : 2 ≤ CFSG.Open.pRank p (P : Subgroup K)) :
    NormalizerMovesLines p (P : Subgroup K) := by
  intro A hAP hA
  obtain ⟨g, hgP, hgA⟩ := hWC P hab hrank A hAP hA
  obtain ⟨z, hzA, hz1⟩ : ∃ z ∈ A, z ≠ 1 := by
    by_contra h
    push Not at h
    have : A = ⊥ := (Subgroup.eq_bot_iff_forall A).2 h
    rw [this, Subgroup.card_bot] at hA
    exact (Fact.out : p.Prime).one_lt.ne hA
  have hgen : ∀ w ∈ A, ∃ k : ℤ, z ^ k = w := by
    have hord : orderOf z = p := by
      have h1 : orderOf z ∣ Nat.card A := Subgroup.orderOf_dvd_natCard A hzA
      rw [hA] at h1
      rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 h1 with h | h
      · exact absurd (orderOf_eq_one_iff.1 h) hz1
      · exact h
    have heq : Subgroup.zpowers z = A := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hzA)
      rw [hA, Nat.card_zpowers, hord]
    intro w hw
    rw [← heq] at hw
    exact Subgroup.mem_zpowers_iff.1 hw
  have hzP : z ∈ (P : Subgroup K) := hAP hzA
  have hgz : g * z * g⁻¹ ∈ (P : Subgroup K) :=
    hgP ⟨z, hzA, by simp [MulAut.conj_apply]⟩
  obtain ⟨n, hn, hnz⟩ := P.conj_eq_normalizer_conj_of_mem z g⁻¹ hzP (by rw [inv_inv]; exact hgz)
  have hnz' : g * z * g⁻¹ = n⁻¹ * z * n := by simpa using hnz
  have hkey : ∀ k : ℤ, g * z ^ k * g⁻¹ = n⁻¹ * z ^ k * n := fun k => by
    have e1 : g * z ^ k * g⁻¹ = (g * z * g⁻¹) ^ k := (conj_zpow).symm
    have e2 : n⁻¹ * z ^ k * n = (n⁻¹ * z * n) ^ k := by
      rw [show n⁻¹ * z * n = n⁻¹ * z * n⁻¹⁻¹ by simp, conj_zpow]
      simp
    rw [e1, e2, hnz']
  refine ⟨n⁻¹, (Subgroup.normalizer ((P : Subgroup K) : Set K)).inv_mem hn, fun heq => hgA ?_⟩
  have hmaps : A.map (MulAut.conj g).toMonoidHom = A.map (MulAut.conj n⁻¹).toMonoidHom := by
    ext x
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨k, rfl⟩ := hgen a ha
      refine ⟨z ^ k, Subgroup.zpow_mem _ hzA k, ?_⟩
      simpa [MulAut.conj_apply] using (hkey k).symm
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨k, rfl⟩ := hgen a ha
      refine ⟨z ^ k, Subgroup.zpow_mem _ hzA k, ?_⟩
      simpa [MulAut.conj_apply] using hkey k
  rw [hmaps]
  exact heq

end Burnside

section Cyclic

variable {G : Type} [Group G] [Finite G] {p : ℕ}

theorem pRank_le_one_of_isCyclic (hp : p.Prime) {H : Subgroup G} (hH : IsCyclic H) :
    CFSG.Open.pRank p H ≤ 1 := by
  unfold CFSG.Open.pRank
  apply csSup_le
  · refine ⟨0, ⊥, bot_le, ⟨⟨⟨fun a b => Subsingleton.elim (a * b) (b * a)⟩⟩, fun x hx => ?_⟩,
      by simp⟩
    rw [Subgroup.mem_bot.1 hx, one_pow]
  · rintro i ⟨E, hEH, hE, hcard⟩
    haveI : IsCyclic E := Subgroup.isCyclic_of_le hEH
    have hexp : Monoid.exponent E ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using hE.2 x x.2)
    rw [IsCyclic.exponent_eq_card, hcard] at hexp
    have h1 : p ^ i ≤ p ^ 1 := by
      rw [pow_one]
      exact Nat.le_of_dvd hp.pos hexp
    exact (Nat.pow_le_pow_iff_right hp.one_lt).1 h1

theorem WCOn.of_isCyclic_sylow [Fact p.Prime] (h : ∀ P : Sylow p G, IsCyclic P) : WCOn p G := by
  intro P _ hrank
  exfalso
  have := pRank_le_one_of_isCyclic (p := p) (H := (P : Subgroup G)) Fact.out (h P)
  omega

end Cyclic

section Embedding

variable {K₁ K : Type} [Group K₁] [Finite K₁] [Group K] [Finite K] {p : ℕ}

theorem NormalizerMovesLines.map (ι : K₁ →* K) (hι : Function.Injective ι) {P₁ : Subgroup K₁}
    (h : NormalizerMovesLines p P₁) : NormalizerMovesLines p (P₁.map ι) := by
  intro A hA hcard
  set A₁ : Subgroup K₁ := A.comap ι with hA₁
  have hArange : A ≤ ι.range := fun x hx => by
    obtain ⟨y, -, rfl⟩ := hA hx
    exact ⟨y, rfl⟩
  have hmap : A₁.map ι = A := by
    rw [hA₁, Subgroup.map_comap_eq, inf_of_le_right hArange]
  have hA₁P : A₁ ≤ P₁ := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hA (show ι x ∈ A from hx)
    exact (hι hyx) ▸ hy
  have hcard₁ : Nat.card A₁ = p := by
    rw [← hcard, ← hmap, Subgroup.card_map_of_injective hι]
  obtain ⟨n, hn, hne⟩ := h A₁ hA₁P hcard₁
  refine ⟨ι n, ?_, fun heq => hne ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨n * y * n⁻¹, (Subgroup.mem_normalizer_iff.1 hn y).1 hy, by simp⟩
    · rintro ⟨z, hz, hzx⟩
      refine ⟨n⁻¹ * z * n, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.1 hn (n⁻¹ * z * n)).2
          (by rwa [show n * (n⁻¹ * z * n) * n⁻¹ = z by group])
      · have e : x = (ι n)⁻¹ * (ι n * x * (ι n)⁻¹) * ι n := by group
        rw [e, ← hzx]
        simp
  · have hcomm : ι.comp (MulAut.conj n).toMonoidHom =
        (MulAut.conj (ι n)).toMonoidHom.comp ι := by
      ext x
      simp [MulAut.conj_apply]
    have hmap2 : (A₁.map (MulAut.conj n).toMonoidHom).map ι = A₁.map ι := by
      rw [Subgroup.map_map, hcomm, ← Subgroup.map_map, hmap]
      exact heq
    exact Subgroup.map_injective hι hmap2

theorem WCOn.of_subgroup_sylow [Fact p.Prime] (ι : K₁ →* K) (hι : Function.Injective ι)
    (P₁ : Sylow p K₁) (hcard : Nat.card (P₁ : Subgroup K₁) = p ^ (Nat.card K).factorization p)
    (h : IsMulCommutative (P₁ : Subgroup K₁) → 2 ≤ CFSG.Open.pRank p (P₁ : Subgroup K₁) →
      NormalizerMovesLines p (P₁ : Subgroup K₁)) : WCOn p K := by
  have hcard' : Nat.card ((P₁ : Subgroup K₁).map ι) = p ^ (Nat.card K).factorization p := by
    rw [Subgroup.card_map_of_injective hι, hcard]
  let P₀ : Sylow p K := Sylow.ofCard _ hcard'
  have hP₀ : (P₀ : Subgroup K) = (P₁ : Subgroup K₁).map ι := Sylow.coe_ofCard _ _
  refine WCOn.of_normalizerMovesLines P₀ fun hab hrank => ?_
  rw [hP₀] at hab hrank ⊢
  have hab₁ : IsMulCommutative (P₁ : Subgroup K₁) := by
    refine ⟨⟨fun a b => Subtype.ext (hι ?_)⟩⟩
    have h1 := congrArg Subtype.val (hab.is_comm.comm ⟨ι a, a, a.2, rfl⟩ ⟨ι b, b, b.2, rfl⟩)
    simpa [map_mul] using h1
  have hrank₁ : 2 ≤ CFSG.Open.pRank p (P₁ : Subgroup K₁) := by
    rwa [CFSG.PreuniquenessRankFour.Helpers.pRank_map_of_injective p Fact.out ι hι] at hrank
  exact (h hab₁ hrank₁).map ι hι

end Embedding

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure
