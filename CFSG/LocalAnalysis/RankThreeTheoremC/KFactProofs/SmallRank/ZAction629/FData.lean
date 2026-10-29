module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZAction629.Basic
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]
variable {f : ℕ} {F : Subgroup K}

theorem fdata_conj_mem_centralizer {w : K} (hw : w ∈ normalizer (F : Set K)) :
    ∀ h ∈ centralizer (F : Set K), w * h * w⁻¹ ∈ centralizer (F : Set K) := by
  intro h hh
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  have hg' : w⁻¹ * g * w ∈ (F : Set K) := by
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem hw) g).1 hg
    rwa [inv_inv] at this
  have hcomm' : (w⁻¹ * g * w) * h = h * (w⁻¹ * g * w) :=
    Subgroup.mem_centralizer_iff.1 hh _ hg'
  calc g * (w * h * w⁻¹) = w * ((w⁻¹ * g * w) * h) * w⁻¹ := by group
    _ = w * (h * (w⁻¹ * g * w)) * w⁻¹ := by rw [hcomm']
    _ = w * h * w⁻¹ * g := by group

theorem fdata_normalizes_inf {S : Subgroup K} {z : K} (hzS : z ∈ normalizer (S : Set K))
    (hzF : z ∈ normalizer (F : Set K)) :
    z ∈ normalizer ((S ⊓ centralizer (F : Set K) : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have hS : h ∈ S ↔ z * h * z⁻¹ ∈ S := Subgroup.mem_normalizer_iff.1 hzS h
  have hC : h ∈ centralizer (F : Set K) ↔ z * h * z⁻¹ ∈ centralizer (F : Set K) := by
    constructor
    · exact fdata_conj_mem_centralizer hzF h
    · intro hh
      have := fdata_conj_mem_centralizer (inv_mem hzF) _ hh
      rwa [show z⁻¹ * (z * h * z⁻¹) * z⁻¹⁻¹ = h by group] at this
  simp only [SetLike.mem_coe, Subgroup.mem_inf]
  exact and_congr hS hC

theorem FData.inv_of_centralizer_eq_bot (hF : FData f F) {e : K}
    (he : e ∈ normalizer (F : Set K)) (he2 : e ^ 2 = 1)
    (hC : F ⊓ centralizer ({e} : Set K) = ⊥) : ∀ a ∈ F, e * a * e⁻¹ = a⁻¹ := by
  intro a ha
  have hb : e * a * e⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.1 he a).1 ha
  have hee : e * e = 1 := by rw [← pow_two]; exact he2
  have hcomm' : a * (e * a * e⁻¹) = (e * a * e⁻¹) * a := hF.comm a ha _ hb
  have hconj : e * (a * (e * a * e⁻¹)) * e⁻¹ = a * (e * a * e⁻¹) := by
    calc e * (a * (e * a * e⁻¹)) * e⁻¹ = (e * a * e⁻¹) * ((e * e) * a * (e * e)⁻¹) := by group
      _ = (e * a * e⁻¹) * a := by rw [hee, one_mul, inv_one, mul_one]
      _ = a * (e * a * e⁻¹) := hcomm'.symm
  have hcent : (a * (e * a * e⁻¹)) * e = e * (a * (e * a * e⁻¹)) := by
    calc (a * (e * a * e⁻¹)) * e = (e * (a * (e * a * e⁻¹)) * e⁻¹) * e := by rw [hconj]
      _ = e * (a * (e * a * e⁻¹)) := by group
  have hmem : a * (e * a * e⁻¹) ∈ F ⊓ centralizer ({e} : Set K) :=
    Subgroup.mem_inf.2 ⟨mul_mem ha hb, Subgroup.mem_centralizer_singleton_iff.2 hcent⟩
  rw [hC, Subgroup.mem_bot] at hmem
  exact (inv_eq_of_mul_eq_one_right hmem).symm

theorem FData.false_of_klein (hF : FData f F) {e₁ e₂ : K} (h₁ : e₁ ∈ normalizer (F : Set K))
    (h₂ : e₂ ∈ normalizer (F : Set K)) (h1sq : e₁ ^ 2 = 1) (h2sq : e₂ ^ 2 = 1) (hne : e₁ ≠ e₂)
    (hcomm : e₁ * e₂ = e₂ * e₁) (hC₁ : F ⊓ centralizer ({e₁} : Set K) = ⊥)
    (hC₂ : F ⊓ centralizer ({e₂} : Set K) = ⊥)
    (hC₁₂ : F ⊓ centralizer ({e₁ * e₂} : Set K) = ⊥) : False := by
  obtain ⟨⟨a, ha⟩, hne1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hF.ne
  have ha1 : a ≠ 1 := fun h => hne1 (Subtype.ext h)
  have i1 : ∀ x ∈ F, e₁ * x * e₁⁻¹ = x⁻¹ := hF.inv_of_centralizer_eq_bot h₁ h1sq hC₁
  have i2 : ∀ x ∈ F, e₂ * x * e₂⁻¹ = x⁻¹ := hF.inv_of_centralizer_eq_bot h₂ h2sq hC₂
  have h12sq : (e₁ * e₂) ^ 2 = 1 := by
    rw [pow_two]
    calc e₁ * e₂ * (e₁ * e₂) = e₁ * (e₂ * e₁) * e₂ := by group
      _ = e₁ * (e₁ * e₂) * e₂ := by rw [← hcomm]
      _ = (e₁ * e₁) * (e₂ * e₂) := by group
      _ = 1 := by rw [← pow_two, ← pow_two, h1sq, h2sq, one_mul]
  have i12 : ∀ x ∈ F, (e₁ * e₂) * x * (e₁ * e₂)⁻¹ = x⁻¹ :=
    hF.inv_of_centralizer_eq_bot (mul_mem h₁ h₂) h12sq hC₁₂
  have hfix : (e₁ * e₂) * a * (e₁ * e₂)⁻¹ = a := by
    calc (e₁ * e₂) * a * (e₁ * e₂)⁻¹ = e₁ * (e₂ * a * e₂⁻¹) * e₁⁻¹ := by group
      _ = e₁ * a⁻¹ * e₁⁻¹ := by rw [i2 a ha]
      _ = (e₁ * a * e₁⁻¹)⁻¹ := by group
      _ = a := by rw [i1 a ha, inv_inv]
  have hinv : a⁻¹ = a := by
    rw [← i12 a ha, hfix]
  have hsq : a * a = 1 := by
    calc a * a = a * a⁻¹ := by rw [hinv]
      _ = 1 := mul_inv_cancel a
  have ha2 : a ^ 2 = 1 := by rw [pow_two]; exact hsq
  have hcop : Nat.Coprime 2 f :=
    (Nat.coprime_primes Nat.prime_two hF.prime).2 (Ne.symm hF.odd)
  have hg : a ^ (Nat.gcd 2 f) = 1 := pow_gcd_eq_one.2 ⟨ha2, hF.exp a ha⟩
  rw [Nat.Coprime.gcd_eq_one hcop, pow_one] at hg
  exact ha1 hg

theorem faithful {S : Subgroup K} {z : K} (hF : F ≠ ⊥) (hzF : zpowers z ≤ normalizer (F : Set K))
    (hzS : zpowers z ≤ normalizer (S : Set K))
    (hb : ∀ S₀ : Subgroup K, S₀ ≤ S → S₀ ≠ ⊥ → zpowers z ≤ normalizer (S₀ : Set K) →
      F ⊓ centralizer (S₀ : Set K) = ⊥) :
    ∀ s ∈ S, (∀ a ∈ F, s * a = a * s) → s = 1 := by
  intro s hs hsF
  have hzF' : z ∈ normalizer (F : Set K) := hzF (Subgroup.mem_zpowers z)
  have hzS' : z ∈ normalizer (S : Set K) := hzS (Subgroup.mem_zpowers z)
  have hz₀ : zpowers z ≤ normalizer ((S ⊓ centralizer (F : Set K) : Subgroup K) : Set K) :=
    Subgroup.zpowers_le.2 (fdata_normalizes_inf hzS' hzF')
  have hbot : S ⊓ centralizer (F : Set K) = ⊥ := by
    by_contra hne
    have h1 := hb (S ⊓ centralizer (F : Set K)) inf_le_left hne hz₀
    have hFle : F ≤ centralizer ((S ⊓ centralizer (F : Set K) : Subgroup K) : Set K) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : x ∈ S ⊓ centralizer (F : Set K) := hx
      exact ((Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hx').2) a ha).symm
    rw [inf_eq_left.2 hFle] at h1
    exact hF h1
  have hsS₀ : s ∈ S ⊓ centralizer (F : Set K) :=
    Subgroup.mem_inf.2 ⟨hs, Subgroup.mem_centralizer_iff.2 (fun a ha => (hsF a ha).symm)⟩
  rw [hbot, Subgroup.mem_bot] at hsS₀
  exact hsS₀

theorem card_le_of_pRank_le {E : Subgroup K} (hf : f.Prime) (hE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a)
    (hE' : ∀ a ∈ E, a ^ f = 1) {r : ℕ} (h : CFSG.Open.pRank f E ≤ r) : Nat.card E ≤ f ^ r := by
  haveI : Fact f.Prime := ⟨hf⟩
  have hP : IsPGroup f E := by
    intro g
    exact ⟨1, Subtype.ext (by
      rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
      exact hE' g.1 g.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.exists_card_eq hP
  have hEab : CFSG.Open.IsElemAbelian f E :=
    ⟨⟨⟨fun a b => Subtype.ext (hE a.1 a.2 b.1 b.2)⟩⟩, fun x hx => hE' x hx⟩
  have hkr : k ≤ CFSG.Open.pRank f E :=
    CFSG.SectionRank.le_pRank hf.one_lt le_rfl hEab hk
  rw [hk]
  exact Nat.pow_le_pow_right hf.pos (hkr.trans h)
end

section
open Subgroup
open scoped commutatorElement

variable {K : Type} [Group K] [Finite K]

variable {f : ℕ} {F : Subgroup K}

theorem swap_conj_mem {x : K} (hx : x ∈ normalizer (F : Set K)) {a : K} (ha : a ∈ F) :
    x * a * x⁻¹ ∈ F :=
  (Subgroup.mem_normalizer_iff.mp hx a).mp ha

theorem swap_half (hf : f.Prime) (hf2 : f ≠ 2) : ∃ m : ℕ, 2 * m = f + 1 := by
  rcases hf.eq_two_or_odd with h | h
  · exact absurd h hf2
  · exact ⟨(f + 1) / 2, by omega⟩

theorem swap_mem_H {g x : K} (hxF : x ∈ F) (hx : g * x * g⁻¹ = x) :
    x ∈ F ⊓ centralizer ({g} : Set K) :=
  Subgroup.mem_inf.mpr
    ⟨hxF, Subgroup.mem_centralizer_singleton_iff.mpr (mul_inv_eq_iff_eq_mul.mp hx).symm⟩

theorem swap_commute_of_mem {g x : K} (hx : x ∈ F ⊓ centralizer ({g} : Set K)) :
    Commute x g :=
  Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hx).2

theorem FData.card_eq_sq_of_swap (hF : FData f F) {g h t' : K}
    (hg : g ∈ normalizer (F : Set K)) (hh : h ∈ normalizer (F : Set K))
    (ht' : t' ∈ normalizer (F : Set K)) (hg2 : g ^ 2 = 1)
    (ht'inv : ∀ a ∈ F, t' * a * t'⁻¹ = a⁻¹) (hcomm : t' * g = g * t')
    (hswap : h * g * h⁻¹ = t' * g) :
    Nat.card F = Nat.card ↥(F ⊓ centralizer ({g} : Set K)) ^ 2 ∧
      ∀ a ∈ F, ∃ b ∈ F ⊓ centralizer ({g} : Set K), ∃ b' ∈ F ⊓ centralizer ({g} : Set K),
        a = b * (h * b' * h⁻¹) := by
  obtain ⟨m, hm⟩ := swap_half hF.prime hF.odd
  have hgg : g * g = 1 := by rw [← pow_two]; exact hg2
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
  have hdec : ∀ a ∈ F, ∃ b ∈ F ⊓ centralizer ({g} : Set K),
      ∃ c ∈ F, a = b * c ∧ g * c * g⁻¹ = c⁻¹ := by
    intro a ha
    have hBa : g * (g * a * g⁻¹) * g⁻¹ = a := by
      rw [hginv]
      calc g * (g * a * g) * g = (g * g) * a * (g * g) := by group
        _ = a := by rw [hgg, one_mul, mul_one]
    obtain ⟨a', ha'F, hA, hB⟩ : ∃ a' ∈ F, g * a * g⁻¹ = a' ∧ g * a' * g⁻¹ = a :=
      ⟨g * a * g⁻¹, swap_conj_mem hg ha, rfl, hBa⟩
    have hB1 : g * (a * a') * g⁻¹ = a' * a := by
      calc g * (a * a') * g⁻¹ = (g * a * g⁻¹) * (g * a' * g⁻¹) := by group
        _ = a' * a := by rw [hA, hB]
    have hC1 : g * (a * a'⁻¹) * g⁻¹ = (a * a'⁻¹)⁻¹ := by
      calc g * (a * a'⁻¹) * g⁻¹ = (g * a * g⁻¹) * (g * a' * g⁻¹)⁻¹ := by group
        _ = a' * a⁻¹ := by rw [hA, hB]
        _ = (a * a'⁻¹)⁻¹ := by group
    have hab1 : a * a' ∈ F := mul_mem ha ha'F
    have hab2 : a * a'⁻¹ ∈ F := mul_mem ha (inv_mem ha'F)
    have hcomm1 : Commute (a * a') (a * a'⁻¹) := hF.comm _ hab1 _ hab2
    have hsq : (a * a') * (a * a'⁻¹) = a ^ 2 := by
      calc (a * a') * (a * a'⁻¹) = a * (a' * a) * a'⁻¹ := by group
        _ = a * (a * a') * a'⁻¹ := by rw [hF.comm a' ha'F a ha]
        _ = a * a := by group
        _ = a ^ 2 := (sq a).symm
    have hbc : (a * a') ^ m * (a * a'⁻¹) ^ m = a := by
      rw [← hcomm1.mul_pow, hsq, ← pow_mul, hm, pow_succ, hF.exp a ha, one_mul]
    have hbg : g * (a * a') ^ m * g⁻¹ = (a * a') ^ m := by
      rw [← conj_pow, hB1, hF.comm a' ha'F a ha]
    have hcg : g * (a * a'⁻¹) ^ m * g⁻¹ = ((a * a'⁻¹) ^ m)⁻¹ := by
      rw [← conj_pow, hC1, inv_pow]
    exact ⟨(a * a') ^ m, swap_mem_H (pow_mem hab1 m) hbg, (a * a'⁻¹) ^ m, pow_mem hab2 m,
      hbc.symm, hcg⟩
  have hsurj : ∀ a ∈ F, ∃ b ∈ F ⊓ centralizer ({g} : Set K),
      ∃ b' ∈ F ⊓ centralizer ({g} : Set K), a = b * (h * b' * h⁻¹) := by
    intro a ha
    obtain ⟨b, hbG, c, hcF, hac, hgc⟩ := hdec a ha
    have hh' : h⁻¹ ∈ normalizer (F : Set K) := inv_mem hh
    have hb'F : h⁻¹ * c * h ∈ F := by
      have := swap_conj_mem hh' hcF
      rwa [inv_inv] at this
    have hgb' : g * (h⁻¹ * c * h) * g⁻¹ = h⁻¹ * c * h := by
      have e2 : t' * g * c * (t' * g)⁻¹ = c := by
        calc t' * g * c * (t' * g)⁻¹ = t' * (g * c * g⁻¹) * t'⁻¹ := by group
          _ = t' * c⁻¹ * t'⁻¹ := by rw [hgc]
          _ = (t' * c * t'⁻¹)⁻¹ := by group
          _ = c := by rw [ht'inv c hcF, inv_inv]
      calc g * (h⁻¹ * c * h) * g⁻¹
          = h⁻¹ * ((h * g * h⁻¹) * c * (h * g * h⁻¹)⁻¹) * h := by group
        _ = h⁻¹ * c * h := by rw [hswap, e2]
    refine ⟨b, hbG, h⁻¹ * c * h, swap_mem_H hb'F hgb', ?_⟩
    rw [show h * (h⁻¹ * c * h) * h⁻¹ = c by group]
    exact hac
  have hmul : ∀ p : ↥(F ⊓ centralizer ({g} : Set K)) × ↥(F ⊓ centralizer ({g} : Set K)),
      (p.1 : K) * (h * (p.2 : K) * h⁻¹) ∈ F := fun p =>
    mul_mem (Subgroup.mem_inf.mp p.1.2).1 (swap_conj_mem hh (Subgroup.mem_inf.mp p.2.2).1)
  let φ : ↥(F ⊓ centralizer ({g} : Set K)) × ↥(F ⊓ centralizer ({g} : Set K)) → ↥F :=
    fun p => ⟨(p.1 : K) * (h * (p.2 : K) * h⁻¹), hmul p⟩
  have hφinj : Function.Injective φ := by
    rintro ⟨⟨b₁, hb₁⟩, ⟨b₁', hb₁'⟩⟩ ⟨⟨b₂, hb₂⟩, ⟨b₂', hb₂'⟩⟩ hφ
    have hval : b₁ * (h * b₁' * h⁻¹) = b₂ * (h * b₂' * h⁻¹) := congrArg Subtype.val hφ
    have hb₁F : b₁ ∈ F := (Subgroup.mem_inf.mp hb₁).1
    have hb₂F : b₂ ∈ F := (Subgroup.mem_inf.mp hb₂).1
    have hc₁ : Commute b₁ g := swap_commute_of_mem hb₁
    have hc₂ : Commute b₂ g := swap_commute_of_mem hb₂
    have hd₁ : Commute b₁' g := swap_commute_of_mem hb₁'
    have hd₂ : Commute b₂' g := swap_commute_of_mem hb₂'
    have hu_F : b₂⁻¹ * b₁ ∈ F := mul_mem (inv_mem hb₂F) hb₁F
    have hu_c : Commute (b₂⁻¹ * b₁) g := (hc₂.inv_left).mul_left hc₁
    have hx_c : Commute (b₂' * b₁'⁻¹) g := hd₂.mul_left hd₁.inv_left
    have hu_eq : b₂⁻¹ * b₁ = h * (b₂' * b₁'⁻¹) * h⁻¹ := by
      calc b₂⁻¹ * b₁ = b₂⁻¹ * (b₁ * (h * b₁' * h⁻¹)) * (h * b₁' * h⁻¹)⁻¹ := by group
        _ = b₂⁻¹ * (b₂ * (h * b₂' * h⁻¹)) * (h * b₁' * h⁻¹)⁻¹ := by rw [hval]
        _ = h * (b₂' * b₁'⁻¹) * h⁻¹ := by group
    have hgx : g * (b₂' * b₁'⁻¹) * g⁻¹ = b₂' * b₁'⁻¹ :=
      mul_inv_eq_iff_eq_mul.mpr hx_c.symm.eq
    have hTu : (h * g * h⁻¹) * (b₂⁻¹ * b₁) * (h * g * h⁻¹)⁻¹ = b₂⁻¹ * b₁ := by
      rw [hu_eq]
      calc (h * g * h⁻¹) * (h * (b₂' * b₁'⁻¹) * h⁻¹) * (h * g * h⁻¹)⁻¹
          = h * (g * (b₂' * b₁'⁻¹) * g⁻¹) * h⁻¹ := by group
        _ = h * (b₂' * b₁'⁻¹) * h⁻¹ := by rw [hgx]
    rw [hswap] at hTu
    have hgu : g * (b₂⁻¹ * b₁) * g⁻¹ = b₂⁻¹ * b₁ :=
      mul_inv_eq_iff_eq_mul.mpr hu_c.symm.eq
    have ht'u : t' * (b₂⁻¹ * b₁) * t'⁻¹ = b₂⁻¹ * b₁ := by
      calc t' * (b₂⁻¹ * b₁) * t'⁻¹ = t' * (g * (b₂⁻¹ * b₁) * g⁻¹) * t'⁻¹ := by rw [hgu]
        _ = (t' * g) * (b₂⁻¹ * b₁) * (t' * g)⁻¹ := by group
        _ = b₂⁻¹ * b₁ := hTu
    have hinv : (b₂⁻¹ * b₁)⁻¹ = b₂⁻¹ * b₁ := (ht'inv _ hu_F).symm.trans ht'u
    have hsq1 : (b₂⁻¹ * b₁) * (b₂⁻¹ * b₁) = 1 := mul_eq_one_iff_eq_inv.mpr hinv.symm
    have hu1 : b₂⁻¹ * b₁ = 1 := by
      calc b₂⁻¹ * b₁ = (b₂⁻¹ * b₁) ^ (f + 1) := by
            rw [pow_succ, hF.exp _ hu_F, one_mul]
        _ = (b₂⁻¹ * b₁) ^ (2 * m) := by rw [hm]
        _ = 1 := by rw [pow_mul, pow_two, hsq1, one_pow]
    have hb12 : b₂ = b₁ := inv_mul_eq_one.mp hu1
    rw [← hb12] at hval
    have hX : h * b₁' * h⁻¹ = h * b₂' * h⁻¹ := mul_left_cancel hval
    have hb1'' : b₁' = b₂' := by
      calc b₁' = h⁻¹ * (h * b₁' * h⁻¹) * h := by group
        _ = h⁻¹ * (h * b₂' * h⁻¹) * h := by rw [hX]
        _ = b₂' := by group
    exact Prod.ext (Subtype.ext hb12.symm) (Subtype.ext hb1'')
  have hφsurj : Function.Surjective φ := by
    intro a
    obtain ⟨b, hb, b', hb', hab⟩ := hsurj a.1 a.2
    exact ⟨(⟨b, hb⟩, ⟨b', hb'⟩), Subtype.ext hab.symm⟩
  have hcardF : Nat.card ↥F
      = Nat.card (↥(F ⊓ centralizer ({g} : Set K)) × ↥(F ⊓ centralizer ({g} : Set K))) :=
    (Nat.card_congr (Equiv.ofBijective φ ⟨hφinj, hφsurj⟩)).symm
  refine ⟨?_, hsurj⟩
  rw [hcardF, Nat.card_prod, sq]
end

section
open Subgroup

variable {K : Type} [Group K] [Finite K]
variable {f : ℕ} {F : Subgroup K}

theorem scalarCyc_pow_eq_of_modEq {G : Type*} [Monoid G] {a : G} {q m n : ℕ} (ha : a ^ q = 1)
    (h : m ≡ n [MOD q]) : a ^ m = a ^ n := by
  have key : ∀ k : ℕ, a ^ k = a ^ (k % q) := fun k => by
    conv_lhs => rw [← Nat.mod_add_div k q, pow_add, pow_mul, ha, one_pow, mul_one]
  have h' : m % q = n % q := h
  rw [key m, key n, h']

theorem FData.isCyclic_of_scalar (hF : FData f F) {C : Subgroup K}
    (hCF : C ≤ normalizer (F : Set K))
    (hfaith : ∀ c ∈ C, (∀ a ∈ F, c * a = a * c) → c = 1)
    (hscalar : ∀ c ∈ C, ∃ n : ℕ, ∀ a ∈ F, c * a * c⁻¹ = a ^ n) : IsCyclic C := by
  haveI : Fact f.Prime := ⟨hF.prime⟩
  obtain ⟨a₀, ha₀F, ha₀⟩ : ∃ a₀ ∈ F, a₀ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hF.ne
    rw [Subgroup.eq_bot_iff_forall]
    exact hcon
  have ha₀f : a₀ ^ f = 1 := hF.exp a₀ ha₀F
  have hord : orderOf a₀ = f := orderOf_eq_prime ha₀f ha₀
  choose! N hN using hscalar
  have hconj : ∀ c ∈ C, c * a₀ * c⁻¹ = a₀ ^ N c := fun c hc => hN c hc a₀ ha₀F
  have hmod : ∀ c ∈ C, ∀ m : ℕ, c * a₀ * c⁻¹ = a₀ ^ m →
      ((N c : ℕ) : ZMod f) = ((m : ℕ) : ZMod f) := by
    intro c hc m hm
    rw [hconj c hc] at hm
    have h1 : N c ≡ m [MOD orderOf a₀] := pow_eq_pow_iff_modEq.mp hm
    rw [hord] at h1
    exact (ZMod.natCast_eq_natCast_iff (N c) m f).mpr h1
  have hone : ((N 1 : ℕ) : ZMod f) = 1 := by
    have h := hmod 1 C.one_mem 1 (by simp)
    rw [Nat.cast_one] at h
    exact h
  have hmul : ∀ c ∈ C, ∀ c' ∈ C,
      ((N (c * c') : ℕ) : ZMod f) = ((N c : ℕ) : ZMod f) * ((N c' : ℕ) : ZMod f) := by
    intro c hc c' hc'
    rw [← Nat.cast_mul]
    apply hmod (c * c') (C.mul_mem hc hc') (N c * N c')
    calc c * c' * a₀ * (c * c')⁻¹ = c * (c' * a₀ * c'⁻¹) * c⁻¹ := by group
      _ = c * (a₀ ^ N c') * c⁻¹ := by rw [hconj c' hc']
      _ = (c * a₀ * c⁻¹) ^ N c' := conj_pow.symm
      _ = (a₀ ^ N c) ^ N c' := by rw [hconj c hc]
      _ = a₀ ^ (N c * N c') := (pow_mul a₀ (N c) (N c')).symm
  let φ : ↥C →* ZMod f :=
    { toFun := fun c => ((N c.1 : ℕ) : ZMod f)
      map_one' := hone
      map_mul' := fun x y => hmul x.1 x.2 y.1 y.2 }
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hx' : ((N x.1 : ℕ) : ZMod f) = 1 := hx
    have hNx : N x.1 ≡ 1 [MOD f] :=
      (ZMod.natCast_eq_natCast_iff (N x.1) 1 f).mp (hx'.trans Nat.cast_one.symm)
    have hcomm : ∀ a ∈ F, x.1 * a = a * x.1 := by
      intro a ha
      have h1 : x.1 * a * x.1⁻¹ = a := by
        rw [hN x.1 x.2 a ha]
        exact (scalarCyc_pow_eq_of_modEq (hF.exp a ha) hNx).trans (pow_one a)
      calc x.1 * a = (x.1 * a * x.1⁻¹) * x.1 := by group
        _ = a * x.1 := by rw [h1]
    exact Subtype.ext (hfaith x.1 x.2 hcomm)
  exact isCyclic_of_injective_ringHom φ hinj
end

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.ZA629
