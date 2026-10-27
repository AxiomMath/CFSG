module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms
import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC

open Subgroup CFSG.Open
open CFSG.ComponentClassification.PerfectAutomorphisms (centerQuotientHom onCenterQuotient_apply_mk
  centerQuotientHom_injective hom_eq_one_of_commutative)

@[expose] noncomputable def l212in_descend {L X : Type} [Group L] [Group X]
    (e : L ⧸ center L ≃* X) : MulAut L →* MulAut X :=
  (MulAut.congr e).toMonoidHom.comp (centerQuotientHom L)

theorem l212in_descend_apply {L X : Type} [Group L] [Group X] (e : L ⧸ center L ≃* X)
    (α : MulAut L) (l : L) :
    l212in_descend e α (e (QuotientGroup.mk l)) = e (QuotientGroup.mk (α l)) := by
  change e (centerQuotientHom L α (e.symm (e (QuotientGroup.mk l)))) = _
  rw [MulEquiv.symm_apply_apply]
  exact congrArg e (onCenterQuotient_apply_mk α l)

theorem l212in_descend_injective {L X : Type} [Group L] [Group X] [Group.IsPerfect L]
    (e : L ⧸ center L ≃* X) : Function.Injective (l212in_descend e) :=
  (MulAut.congr e).injective.comp (centerQuotientHom_injective L)

theorem l212in_descend_conj {L X : Type} [Group L] [Group X] (e : L ⧸ center L ≃* X) (l : L) :
    l212in_descend e (MulAut.conj l) = MulAut.conj (e (QuotientGroup.mk l)) := by
  have h := CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_conj l
  change MulAut.congr e (centerQuotientHom L (MulAut.conj l)) = _
  rw [h]
  exact CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e _

theorem l212in_dvd_of_pow_mem {p : ℕ} (hp : p.Prime) {C : Type} [CommGroup C] {n : ℕ} {d : C}
    (hd : ¬ ∃ c : C, d = c ^ n) (hdp : ∃ c : C, d ^ p = c ^ n) {k : ℤ}
    (hdk : ∃ c : C, d ^ k = c ^ n) : (p : ℤ) ∣ k := by
  let N : Subgroup C := (powMonoidHom n : C →* C).range
  let g : C ⧸ N := QuotientGroup.mk d
  have hmem : ∀ x : C, x ∈ N ↔ ∃ c : C, x = c ^ n := by
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨c, by simp⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c, by simp⟩
  have hg1 : g ≠ 1 := by
    intro h
    exact hd ((hmem d).1 ((QuotientGroup.eq_one_iff d).1 h))
  have hgp : g ^ p = 1 := by
    obtain ⟨c, hc⟩ := hdp
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, hmem]
    exact ⟨c, hc⟩
  have hgk : g ^ k = 1 := by
    obtain ⟨c, hc⟩ := hdk
    rw [← QuotientGroup.mk_zpow, QuotientGroup.eq_one_iff, hmem]
    exact ⟨c, hc⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf g = p := orderOf_eq_prime hgp hg1
  have := (orderOf_dvd_iff_zpow_eq_one (x := g) (i := k)).2 hgk
  rwa [hord] at this

theorem l212in_modp_one_of_not_mem {p : ℕ} (hp : p.Prime) {G : Type} [Group G] (Dg : Subgroup G)
    (u v : G) (b : ℕ) (hab : v * u * v⁻¹ * u⁻¹ ∈ Dg) (hup : u ^ p = 1) (hu : u ∉ Dg)
    (hv : v * u * v⁻¹ = u ^ b) : (b : ZMod p) = 1 := by
  have hk : u ^ ((b : ℤ) - 1) ∈ Dg := by
    have : v * u * v⁻¹ * u⁻¹ = u ^ ((b : ℤ) - 1) := by
      rw [hv, zpow_sub, zpow_natCast, zpow_one]
    rwa [this] at hab
  by_contra hne
  have hndvd : ¬ (p : ℤ) ∣ ((b : ℤ) - 1) := by
    intro h
    apply hne
    have := (ZMod.intCast_zmod_eq_zero_iff_dvd ((b : ℤ) - 1) p).2 h
    push_cast at this
    exact sub_eq_zero.1 this
  have hcop : IsCoprime (p : ℤ) ((b : ℤ) - 1) :=
    (Irreducible.coprime_iff_not_dvd (Nat.prime_iff_prime_int.1 hp).irreducible).2 hndvd
  obtain ⟨x, y, hxy⟩ := hcop
  apply hu
  have hxy' : (p : ℤ) * x + ((b : ℤ) - 1) * y = 1 := by linear_combination hxy
  have h1 : u = (u ^ (p : ℤ)) ^ x * (u ^ ((b : ℤ) - 1)) ^ y := by
    rw [← zpow_mul, ← zpow_mul, ← zpow_add, hxy', zpow_one]
  rw [h1, zpow_natCast, hup, one_zpow, one_mul]
  exact zpow_mem hk y

theorem l212in_alpha_phi {L X S : Type} [Group L] [Group X] [Group S] [Group.IsPerfect S]
    (e : L ⧸ center L ≃* X) (π : S →* X) (φ : S →* L)
    (hφπ : ∀ s, e (QuotientGroup.mk (φ s)) = π s) (α : MulAut L) (Ã : S →* S)
    (hÃ : ∀ s, π (Ã s) = l212in_descend e α (π s)) (s : S) : α (φ s) = φ (Ã s) := by
  have hcen : ∀ s, (φ (Ã s))⁻¹ * α (φ s) ∈ center L := by
    intro s
    have h1 : e (QuotientGroup.mk (φ (Ã s))) = e (QuotientGroup.mk (α (φ s))) := by
      rw [hφπ, hÃ, ← hφπ, l212in_descend_apply]
    exact QuotientGroup.eq.1 (e.injective h1)
  let f : S →* center L :=
    { toFun := fun s => ⟨(φ (Ã s))⁻¹ * α (φ s), hcen s⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := by
        intro s t
        apply Subtype.ext
        have hc := mem_center_iff.1 (hcen s) (φ (Ã t))⁻¹
        change (φ (Ã (s * t)))⁻¹ * α (φ (s * t)) =
          ((φ (Ã s))⁻¹ * α (φ s)) * ((φ (Ã t))⁻¹ * α (φ t))
        calc (φ (Ã (s * t)))⁻¹ * α (φ (s * t))
            = (φ (Ã t))⁻¹ * ((φ (Ã s))⁻¹ * α (φ s)) * α (φ t) := by
              simp only [map_mul, mul_inv_rev, mul_assoc]
          _ = ((φ (Ã s))⁻¹ * α (φ s)) * (φ (Ã t))⁻¹ * α (φ t) := by rw [hc]
          _ = ((φ (Ã s))⁻¹ * α (φ s)) * ((φ (Ã t))⁻¹ * α (φ t)) := by rw [mul_assoc] }
  have hf : f = 1 := hom_eq_one_of_commutative f
  have h1 := congrArg (fun g : S →* center L => ((g s : center L) : L)) hf
  simp only [f, MonoidHom.coe_mk, OneHom.coe_mk, MonoidHom.one_apply, OneMemClass.coe_one] at h1
  exact (inv_mul_eq_one.1 h1).symm

theorem outDiag_core {p : ℕ} (hp : p.Prime) {L X S D C : Type} [Group L] [Finite L] [Group X]
    [Group S] [Group D] [CommGroup C] {n : ℕ} (hL : IsQuasisimple L) (hZne : center L ≠ ⊥)
    (hZp : IsPGroup p (center L)) (hS : Group.IsPerfect S) (π : S →* X)
    (e : L ⧸ center L ≃* X) (φ : S →* L) (hφπ : ∀ s, e (QuotientGroup.mk (φ s)) = π s)
    (hφ : Function.Surjective φ) (Φ : D →* MulAut X) (det : D →* C)
    (hab : ∀ x y : MulAut X, x * y * x⁻¹ * y⁻¹ ∈ Φ.range)
    (hker : ∀ B, Φ B = 1 → ∃ c : C, det B = c ^ n)
    (hinn : ∀ B, (∃ c : C, det B = c ^ n) → Φ B ∈ (MulAut.conj : X →* MulAut X).range)
    (hlift : ∀ α : MulAut X, ∃ (κ : ℤ) (Ã : S →* S) (t : D → D),
      (∀ s, π (Ã s) = α (π s)) ∧ (∀ s ∈ π.ker, Ã s = s ^ κ) ∧
      (∀ B, α * Φ B * α⁻¹ = Φ (t B)) ∧ (∀ B, det (t B) = det B ^ κ))
    (α δ : MulAut L) (a b : ℕ) (hδp : δ ^ p = 1)
    (hδ : δ ∉ (MulAut.conj : L →* MulAut L).range) (hαδ : α * δ * α⁻¹ = δ ^ b)
    (hαc : ∀ c ∈ center L, c ^ p = 1 → α c = c ^ a) :
    (a : ZMod p) = b ∨ (b : ZMod p) = 1 := by
  haveI : Group.IsPerfect L := ⟨hL.1⟩
  haveI : Group.IsPerfect S := hS
  haveI : Fact p.Prime := ⟨hp⟩
  have hρinj : Function.Injective (l212in_descend e) := l212in_descend_injective e
  have hρδp : (l212in_descend e δ) ^ p = 1 := by rw [← map_pow, hδp, map_one]
  have hρb : l212in_descend e α * l212in_descend e δ * (l212in_descend e α)⁻¹ =
      (l212in_descend e δ) ^ b := by
    rw [← map_inv, ← map_mul, ← map_mul, hαδ, map_pow]
  by_cases hmem : l212in_descend e δ ∈ Φ.range
  · left
    obtain ⟨B, hB⟩ := hmem
    have hnotinn : Φ B ∉ (MulAut.conj : X →* MulAut X).range := by
      rintro ⟨x, hx⟩
      obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective (e.symm x)
      have hxl : x = e (QuotientGroup.mk l) := by rw [hl, MulEquiv.apply_symm_apply]
      apply hδ
      refine ⟨l, hρinj ?_⟩
      rw [l212in_descend_conj, ← hxl, hx, hB]
    have hnotpow : ¬ ∃ c : C, det B = c ^ n := fun h => hnotinn (hinn B h)
    obtain ⟨κ, Ã, t, hπÃ, hÃker, hΦt, hdet⟩ := hlift (l212in_descend e α)
    have hBp : ∃ c : C, det B ^ p = c ^ n := by
      obtain ⟨c, hc⟩ := hker (B ^ p) (by rw [map_pow, hB, hρδp])
      exact ⟨c, by rw [← map_pow]; exact hc⟩
    have hBb : ∃ c : C, det B ^ (κ - (b : ℤ)) = c ^ n := by
      have h1 : Φ ((B ^ b)⁻¹ * t B) = 1 := by
        rw [map_mul, map_inv, map_pow, ← hΦt B, hB, hρb, inv_mul_cancel]
      obtain ⟨c, hc⟩ := hker _ h1
      refine ⟨c, ?_⟩
      rw [← hc, map_mul, map_inv, map_pow, hdet B, zpow_sub, zpow_natCast]
      exact mul_comm _ _
    have hpb : (p : ℤ) ∣ κ - (b : ℤ) := l212in_dvd_of_pow_mem hp hnotpow hBp hBb
    haveI : Nontrivial (center L) := (Subgroup.nontrivial_iff_ne_bot _).2 hZne
    obtain ⟨m, hm, hmcard⟩ := hZp.nontrivial_iff_card.mp inferInstance
    have hdvd : p ∣ Nat.card (center L) := hmcard ▸ dvd_pow_self p hm.ne'
    obtain ⟨c, hcord⟩ := exists_prime_orderOf_dvd_card' p hdvd
    obtain ⟨z, hz, hzc⟩ : ∃ z ∈ π.ker, φ z = (c : L) := by
      obtain ⟨s, hs⟩ := hφ (c : L)
      refine ⟨s, ?_, hs⟩
      rw [MonoidHom.mem_ker, ← hφπ, hs, (QuotientGroup.eq_one_iff (c : L)).2 c.2, map_one]
    have hcp : (c : L) ^ p = 1 := by
      have h1 := pow_orderOf_eq_one c
      rw [hcord] at h1
      exact congrArg Subtype.val h1
    have hcα : α (c : L) = (c : L) ^ a := hαc (c : L) c.2 hcp
    have hαφ := l212in_alpha_phi e π φ hφπ α Ã hπÃ z
    have hκ : α (c : L) = (c : L) ^ κ := by
      rw [← hzc, hαφ, hÃker z hz, map_zpow]
    have hpa : (p : ℤ) ∣ κ - (a : ℤ) := by
      have h1 : (c : L) ^ (κ - (a : ℤ)) = 1 := by
        rw [zpow_sub, zpow_natCast, ← hκ, hcα, mul_inv_cancel]
      have h2 : c ^ (κ - (a : ℤ)) = 1 := Subtype.ext (by simpa using h1)
      have h3 := (orderOf_dvd_iff_zpow_eq_one (x := c) (i := κ - (a : ℤ))).2 h2
      rwa [hcord] at h3
    have ha : ((κ : ℤ) : ZMod p) = (a : ZMod p) := by
      have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (κ - (a : ℤ)) p).2 hpa
      push_cast at h1
      exact sub_eq_zero.1 h1
    have hb : ((κ : ℤ) : ZMod p) = (b : ZMod p) := by
      have h1 := (ZMod.intCast_zmod_eq_zero_iff_dvd (κ - (b : ℤ)) p).2 hpb
      push_cast at h1
      exact sub_eq_zero.1 h1
    exact ha.symm.trans hb
  · right
    exact l212in_modp_one_of_not_mem hp Φ.range _ _ b (hab _ _) hρδp hmem hρb

end CFSG.LocalAnalysis.RankFourTheoremC
