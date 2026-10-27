module

public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67Core

public section

namespace CFSG.GH74.GLS.Stage2.Bender.Thm1

open Subgroup CFSG CFSG.GH74.GLS.Stage2.Signalizer.Odd87
open scoped commutatorElement

section Iso

variable {Y Y' : Type} [Group Y] [Group Y']

theorem fixSub_congr (e : Y ≃* Y') (v : MulAut Y) :
    (fixSub v).map e.toMonoidHom = fixSub (MulAut.congr e v) := by
  ext y'
  obtain ⟨y, rfl⟩ := e.surjective y'
  constructor
  · rintro ⟨c, hc, hce⟩
    have hc' : v c = c := hc
    have : e c = e y := hce
    rw [mem_fixSub]
    rw [← e.injective this] at *
    simp [MulAut.congr_apply, hc']
  · intro h
    rw [mem_fixSub] at h
    refine ⟨y, ?_, rfl⟩
    show v y = y
    have := congrArg e.symm h
    simpa [MulAut.congr_apply] using this


theorem mem_normalizer_map_equiv {G G' : Type} [Group G] [Group G'] (f : G ≃* G') {S : Subgroup G}
    {g : G} (h : g ∈ normalizer (S : Set G)) :
    f g ∈ normalizer ((S.map f.toMonoidHom : Subgroup G') : Set G') := by
  rw [Subgroup.mem_normalizer_iff] at h ⊢
  intro x'
  obtain ⟨x, rfl⟩ := f.surjective x'
  have e1 : f g * f x * (f g)⁻¹ = f (g * x * g⁻¹) := by simp
  rw [e1]
  have m1 : ∀ w : G, f w ∈ S.map f.toMonoidHom ↔ w ∈ S := fun w =>
    Subgroup.mem_map_equiv (f := f) (K := S) (x := f w) |>.trans (by simp)
  rw [m1, m1]
  exact h x

theorem N3Full.map_mulEquiv (e : Y ≃* Y') {V Z : Subgroup (MulAut Y)} (h : N3Full Y V Z) :
    N3Full Y' (V.map (MulAut.congr e).toMonoidHom) (Z.map (MulAut.congr e).toMonoidHom) := by
  rintro _ ⟨v, hv, rfl⟩ hne c' hc'
  have hne' : v ≠ 1 := fun h1 => hne (by rw [h1]; exact map_one _)
  change c' ∈ fixSub (MulAut.congr e v) at hc'
  rw [← fixSub_congr] at hc'
  obtain ⟨c, hc, rfl⟩ := hc'
  have h1 := h v hv hne' c hc
  have hconj : MulAut.conj (e c) = MulAut.congr e (MulAut.conj c) := by
    ext y; simp [MulAut.conj_apply, MulAut.congr_apply]
  show MulAut.conj (e c) ∈ _
  rw [hconj]
  exact mem_normalizer_map_equiv (MulAut.congr e) h1

theorem N3Deriv.map_mulEquiv (e : Y ≃* Y') {V Z : Subgroup (MulAut Y)} (h : N3Deriv Y V Z) :
    N3Deriv Y' (V.map (MulAut.congr e).toMonoidHom) (Z.map (MulAut.congr e).toMonoidHom) := by
  rintro _ ⟨v, hv, rfl⟩ hne c' hc'
  have hne' : v ≠ 1 := fun h1 => hne (by rw [h1]; exact map_one _)
  change c' ∈ ⁅fixSub (MulAut.congr e v), fixSub (MulAut.congr e v)⁆ at hc'
  rw [← fixSub_congr, ← Subgroup.map_commutator] at hc'
  obtain ⟨c, hc, rfl⟩ := hc'
  have h1 := h v hv hne' c hc
  have hconj : MulAut.conj (e c) = MulAut.congr e (MulAut.conj c) := by
    ext y; simp [MulAut.conj_apply, MulAut.congr_apply]
  show MulAut.conj (e c) ∈ _
  rw [hconj]
  exact mem_normalizer_map_equiv (MulAut.congr e) h1

theorem CF67CoreFull.of_mulEquiv [Finite Y] [Finite Y'] (e : Y ≃* Y') (h : CF67CoreFull Y') :
    CF67CoreFull Y := by
  intro hs hn r V Z h2 h3
  have hs' : IsSimpleGroup Y' := by
    have := hs
    exact MulEquiv.isSimpleGroup e.symm
  obtain ⟨a, b, hab⟩ := hn
  have hn' : ∃ a b : Y', a * b ≠ b * a :=
    ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
  exact h hs' hn' r _ _ (h2.map_mulEquiv (MulAut.congr e)) (h3.map_mulEquiv e)

theorem CF67CoreDeriv.of_mulEquiv [Finite Y] [Finite Y'] (e : Y ≃* Y') {r : ℕ}
    (h : CF67CoreDeriv Y' r) : CF67CoreDeriv Y r := by
  intro hs hn V Z h2 h3
  have hs' : IsSimpleGroup Y' := by
    have := hs
    exact MulEquiv.isSimpleGroup e.symm
  obtain ⟨a, b, hab⟩ := hn
  have hn' : ∃ a b : Y', a * b ≠ b * a :=
    ⟨e a, e b, fun h => hab (e.injective (by simpa using h))⟩
  exact h hs' hn' _ _ (h2.map_mulEquiv (MulAut.congr e)) (h3.map_mulEquiv e)

end Iso


section Step

variable {Y : Type} [Group Y]

theorem mulAut_conj_conj (φ : MulAut Y) (a : Y) : φ * MulAut.conj a * φ⁻¹ = MulAut.conj (φ a) := by
  ext y; simp [MulAut.conj_apply]

theorem rstep_fix [Finite Y] {r : ℕ} {V Z : Subgroup (MulAut Y)}
    (hcen : Subgroup.center Y = ⊥) (h2 : N2Cfg Y r V Z) (h3 : N3Full Y V Z) {v : MulAut Y}
    (hv : v ∈ V) (hne : v ≠ 1) {Q : Subgroup Y} (hQle : Q ≤ fixSub v) (hQr : IsPGroup r ↥Q)
    (hQinv : ∀ z ∈ Z, ∀ c ∈ Q, z c ∈ Q) :
    ∀ z ∈ Z, ∀ c ∈ Q, z c = c := by
  obtain ⟨hr, -, -, -, -, -, hZcop, -, -⟩ := h2
  intro z hz c hc
  have : Fact r.Prime := ⟨hr⟩
  have hnorm := h3 v hv hne c (hQle hc)
  have h1 := (Subgroup.mem_normalizer_iff.mp hnorm z).mp hz
  have h4 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ ∈ Z :=
    Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hz)
  have h5 : MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (c * z c⁻¹) := by
    have : z * (MulAut.conj c)⁻¹ * z⁻¹ = MulAut.conj (z c⁻¹) := by
      have := mulAut_conj_conj z c⁻¹
      simpa [map_inv] using this
    calc MulAut.conj c * z * (MulAut.conj c)⁻¹ * z⁻¹
        = MulAut.conj c * (z * (MulAut.conj c)⁻¹ * z⁻¹) := by group
      _ = MulAut.conj (c * z c⁻¹) := by rw [this, map_mul]
  rw [h5] at h4
  have hd : c * z c⁻¹ ∈ Q := by
    have := Subgroup.mul_mem _ hc (Subgroup.inv_mem _ (hQinv z hz c hc))
    simpa using this
  have hZc : Nat.Coprime (Nat.card ↥Z) r := hZcop
  have hordZ : orderOf (MulAut.conj (c * z c⁻¹)) ∣ Nat.card ↥Z := by
    have := orderOf_dvd_natCard (⟨MulAut.conj (c * z c⁻¹), h4⟩ : ↥Z)
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hQr) ⟨c * z c⁻¹, hd⟩
  have hordQ : orderOf (MulAut.conj (c * z c⁻¹)) ∣ r ^ k := by
    have h6 : orderOf (MulAut.conj (c * z c⁻¹)) ∣ orderOf (c * z c⁻¹) :=
      orderOf_map_dvd (MulAut.conj : Y →* MulAut Y) _
    rw [Subgroup.orderOf_mk] at hk
    exact h6.trans (hk ▸ dvd_rfl)
  have hcop : Nat.Coprime (r ^ k) (Nat.card ↥Z) := (Nat.Coprime.pow_left k hZc.symm)
  have hone : orderOf (MulAut.conj (c * z c⁻¹)) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop hordQ hordZ
  have h7 : MulAut.conj (c * z c⁻¹) = 1 := orderOf_eq_one_iff.mp hone
  have h8 : c * z c⁻¹ ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun φ : MulAut Y => φ g) h7
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    have h9 : (c * z c⁻¹) * g * (c * z c⁻¹)⁻¹ = g := this
    calc g * (c * z c⁻¹) = ((c * z c⁻¹) * g * (c * z c⁻¹)⁻¹) * (c * z c⁻¹) := by rw [h9]
      _ = (c * z c⁻¹) * g := by group
  rw [hcen, Subgroup.mem_bot] at h8
  have : z c⁻¹ = c⁻¹ := by
    have := congrArg (fun t => c⁻¹ * t) h8
    simpa using this
  have := congrArg (fun t => t⁻¹) this
  simpa using this

theorem false_of_rstep [Finite Y] {r : ℕ} {V Z : Subgroup (MulAut Y)}
    (hcen : Subgroup.center Y = ⊥) (h2 : N2Cfg Y r V Z) (h3 : N3Full Y V Z) {v : MulAut Y}
    (hv : v ∈ V) (hne : v ≠ 1) {Q : Subgroup Y} (hQle : Q ≤ fixSub v) (hQr : IsPGroup r ↥Q)
    (hQinv : ∀ z ∈ Z, ∀ c ∈ Q, z c ∈ Q)
    (hR : ∀ z : MulAut Y, Odd (orderOf z) → Nat.Coprime (orderOf z) r → (∀ c ∈ Q, z c = c) → z = 1) :
    False := by
  have hfix := rstep_fix hcen h2 h3 hv hne hQle hQr hQinv
  obtain ⟨-, -, -, -, -, hZodd, hZcop, hZbot, -⟩ := h2
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZbot
  have hdvd : orderOf (z : MulAut Y) ∣ Nat.card ↥Z := by
    have := orderOf_dvd_natCard z
    rwa [← Subgroup.orderOf_coe] at this
  have hodd : Odd (orderOf (z : MulAut Y)) := Odd.of_dvd_nat hZodd hdvd
  have hcop : Nat.Coprime (orderOf (z : MulAut Y)) r := Nat.Coprime.coprime_dvd_left hdvd hZcop
  have := hR z hodd hcop (hfix z z.2)
  exact hz1 (Subtype.ext this)

end Step

end CFSG.GH74.GLS.Stage2.Bender.Thm1
