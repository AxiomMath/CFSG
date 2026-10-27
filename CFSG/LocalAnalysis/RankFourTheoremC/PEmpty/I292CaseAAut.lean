module

public import CFSG.LocalAnalysis.ComponentClassification.PerfectAutomorphisms

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA

open CFSG.ComponentClassification.PerfectAutomorphisms Subgroup

variable {Y : Type} [Group Y] (L : Subgroup Y) [L.Normal]

@[expose] noncomputable def theta : Y →* MulAut (↥L ⧸ center ↥L) :=
  (centerQuotientHom ↥L).comp MulAut.conjNormal

theorem theta_mk (y : Y) (l : L) :
    theta L y (QuotientGroup.mk l) = QuotientGroup.mk (MulAut.conjNormal y l) :=
  onCenterQuotient_apply_mk (MulAut.conjNormal y) l

theorem theta_eq_one_iff [Group.IsPerfect ↥L] (y : Y) :
    theta L y = 1 ↔ y ∈ centralizer (L : Set Y) := by
  constructor
  · intro h
    have h1 : centerQuotientHom ↥L (MulAut.conjNormal y) = centerQuotientHom ↥L 1 := by
      rw [map_one]
      exact h
    have h2 : (MulAut.conjNormal y : MulAut L) = 1 := centerQuotientHom_injective ↥L h1
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h3 := congrArg (fun f : MulAut L => ((f ⟨l, hl⟩ : L) : Y)) h2
    simp only [MulAut.conjNormal_apply, MulAut.one_apply] at h3
    calc l * y = y * l * y⁻¹ * y := by rw [h3]
      _ = y * l := by group
  · intro hy
    have h2 : (MulAut.conjNormal y : MulAut L) = 1 := by
      ext l
      simp only [MulAut.conjNormal_apply, MulAut.one_apply]
      have := Subgroup.mem_centralizer_iff.1 hy l l.2
      calc y * (l : Y) * y⁻¹ = (l : Y) * y * y⁻¹ := by rw [← this]
        _ = l := by group
    change centerQuotientHom ↥L (MulAut.conjNormal y) = 1
    rw [h2, map_one]

theorem theta_of_mem (l : L) : theta L (l : Y) = MulAut.conj (QuotientGroup.mk l) := by
  ext z
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective z
  rw [theta_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  congr 1

variable {P' : Type} [Group P'] (eP : (↥L ⧸ center ↥L) ≃* P')

@[expose] noncomputable def thetaP : Y →* MulAut P' :=
  (MulAut.congr eP).toMonoidHom.comp (theta L)

theorem thetaP_apply (y : Y) (z : P') : thetaP L eP y z = eP (theta L y (eP.symm z)) := rfl

theorem thetaP_eq_one_iff [Group.IsPerfect ↥L] (y : Y) :
    thetaP L eP y = 1 ↔ y ∈ centralizer (L : Set Y) := by
  rw [← theta_eq_one_iff L y]
  change MulAut.congr eP (theta L y) = 1 ↔ _
  rw [map_eq_one_iff _ (MulAut.congr eP).injective]

theorem thetaP_of_mem (l : L) :
    thetaP L eP (l : Y) = MulAut.conj (eP (QuotientGroup.mk l)) := by
  change MulAut.congr eP (theta L (l : Y)) = _
  rw [theta_of_mem]
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem mem_of_pow_mem {A : Subgroup Y} {t : Y} {m j : ℕ} (hcop : Nat.Coprime m (2 ^ j))
    (ht : t ^ (2 ^ j) = 1) (hm : t ^ m ∈ A) : t ∈ A := by
  have hc : Nat.Coprime m (orderOf t) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one ht) hcop
  obtain ⟨a, ha⟩ := exists_pow_eq_self_of_coprime hc
  rw [← ha]
  exact pow_mem hm a

theorem eq_one_of_thetaP_mem_inner [Group.IsPerfect ↥L] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hCp : IsPGroup p (centralizer (L : Set Y))) {T : Subgroup Y} (hT : IsPGroup 2 T)
    (hTL : T ⊓ L = ⊥) {t : Y} (ht : t ∈ T)
    (hin : thetaP L eP t ∈ (MulAut.conj : P' →* MulAut P').range) : t = 1 := by
  obtain ⟨z, hz⟩ := hin
  obtain ⟨w, rfl⟩ := eP.surjective z
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective w
  have h1 : thetaP L eP ((l : Y)⁻¹ * t) = 1 := by
    rw [map_mul, map_inv, thetaP_of_mem, hz, inv_mul_cancel]
  have hc : (l : Y)⁻¹ * t ∈ centralizer (L : Set Y) := (thetaP_eq_one_iff L eP _).1 h1
  obtain ⟨k, hk⟩ := hCp ⟨_, hc⟩
  have hk' : ((l : Y)⁻¹ * t) ^ (p ^ k) = 1 := by
    simpa using congrArg Subtype.val hk
  have hcomm : Commute (l : Y) ((l : Y)⁻¹ * t) := by
    have := Subgroup.mem_centralizer_iff.1 hc l l.2
    exact this
  have htl : t = (l : Y) * ((l : Y)⁻¹ * t) := by group
  obtain ⟨j, hj⟩ := hT ⟨t, ht⟩
  have hj' : t ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
  have hpow : t ^ (p ^ k) ∈ L := by
    have : t ^ (p ^ k) = (l : Y) ^ (p ^ k) := by
      conv_lhs => rw [htl]
      rw [hcomm.mul_pow, hk', mul_one]
    rw [this]
    exact pow_mem l.2 _
  have hcop : Nat.Coprime (p ^ k) (2 ^ j) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have htL : t ∈ L := mem_of_pow_mem hcop hj' hpow
  have : t ∈ T ⊓ L := Subgroup.mem_inf.2 ⟨ht, htL⟩
  rw [hTL] at this
  exact this

theorem commute_of_thetaP {T : Subgroup Y} {x : Y} (hxT : x ∈ normalizer (T : Set Y))
    (D : Subgroup (MulAut P')) [D.Normal] (hxD : thetaP L eP x ∈ D)
    (hD : ∀ s ∈ T, thetaP L eP s ∈ D → s = 1) : ∀ t ∈ T, t * x = x * t := by
  intro t ht
  have hxt : x * t⁻¹ * x⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.1 hxT t⁻¹).1 (inv_mem ht)
  have hs : t * (x * t⁻¹ * x⁻¹) ∈ T := mul_mem ht hxt
  have hsD : thetaP L eP (t * (x * t⁻¹ * x⁻¹)) ∈ D := by
    have : thetaP L eP (t * (x * t⁻¹ * x⁻¹)) =
        (thetaP L eP t * thetaP L eP x * (thetaP L eP t)⁻¹) * (thetaP L eP x)⁻¹ := by
      simp only [map_mul, map_inv, mul_assoc]
    rw [this]
    exact mul_mem (Normal.conj_mem ‹D.Normal› _ hxD _) (inv_mem hxD)
  have h1 := hD _ hs hsD
  calc t * x = t * x * t⁻¹ * x⁻¹ * (x * t) := by group
    _ = x * t := by
      have : t * x * t⁻¹ * x⁻¹ = 1 := by
        have : t * (x * t⁻¹ * x⁻¹) = t * x * t⁻¹ * x⁻¹ := by group
        rw [← this]
        exact h1
      rw [this, one_mul]

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.I292CaseA
