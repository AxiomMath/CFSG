module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivialCases

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial

open CFSG.Open

section Aut

variable {K : Type} [Group K]

theorem injective_conj_of_center_eq_bot (hcen : Subgroup.center K = ⊥) :
    Function.Injective (MulAut.conj : K →* MulAut K) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have : g ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro x
    have := congrArg (fun f : MulAut K => f x) hg
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    have h : g * x = x * g := by
      calc g * x = (g * x * g⁻¹) * g := by group
        _ = x * g := by rw [this]
    exact h.symm
  rw [hcen] at this
  exact Subgroup.mem_bot.1 this

theorem mulAut_mul_conj_mul_inv (f : MulAut K) (g : K) :
    f * MulAut.conj g * f⁻¹ = MulAut.conj (f g) := by
  ext x
  simp [MulAut.conj_apply]

theorem normal_range_conj : ((MulAut.conj : K →* MulAut K).range).Normal := by
  refine ⟨fun n hn f => ?_⟩
  obtain ⟨g, rfl⟩ := hn
  exact ⟨f g, (mulAut_mul_conj_mul_inv f g).symm⟩

theorem centralizer_range_conj_eq_bot (hcen : Subgroup.center K = ⊥) :
    Subgroup.centralizer (((MulAut.conj : K →* MulAut K).range : Subgroup (MulAut K)) :
      Set (MulAut K)) = ⊥ := by
  have hinj := injective_conj_of_center_eq_bot hcen
  rw [eq_bot_iff]
  intro f hf
  rw [Subgroup.mem_bot]
  ext x
  have h1 : MulAut.conj x * f = f * MulAut.conj x :=
    Subgroup.mem_centralizer_iff.1 hf _ ⟨x, rfl⟩
  have h2 : f * MulAut.conj x * f⁻¹ = MulAut.conj x := by
    rw [← h1]; group
  rw [mulAut_mul_conj_mul_inv] at h2
  exact hinj h2

noncomputable def mulEquivRangeConj (hcen : Subgroup.center K = ⊥) :
    K ≃* ((MulAut.conj : K →* MulAut K).range) :=
  MonoidHom.ofInjective (injective_conj_of_center_eq_bot hcen)

theorem center_eq_bot_of_mulEquiv {G : Type*} [Group G] (e : K ≃* G)
    (h : Subgroup.center G = ⊥) : Subgroup.center K = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hex : e x ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx z]
  rw [h, Subgroup.mem_bot] at hex
  exact Subgroup.mem_bot.2 (e.injective (by rw [hex, map_one]))

end Aut

section Elementary

theorem eq_one_of_mem_of_mem_of_coprime {G : Type*} [Group G] {p : ℕ} {R W : Subgroup G}
    (hR : IsPGroup p R) (hW : Nat.Coprime p (Nat.card W)) {w : G} (hwR : w ∈ R) (hwW : w ∈ W) :
    w = 1 := by
  obtain ⟨k, hk⟩ := hR ⟨w, hwR⟩
  have h1 : w ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : orderOf w ∣ p ^ k := orderOf_dvd_of_pow_eq_one h1
  have h3 : orderOf w ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hwW
  have h4 : Nat.Coprime (orderOf w) (p ^ k) :=
    Nat.Coprime.pow_right k (Nat.Coprime.coprime_dvd_left h3 hW.symm)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd h4 h2)

variable {K : Type} [Group K]

theorem le_iSup_planes_of_card {p : ℕ} [Fact p.Prime] [Finite K] (U : Subgroup K)
    {n : ℕ} (hn : 2 ≤ n) (hcard : Nat.card U = p ^ n) (hexp : ∀ x ∈ U, x ^ p = 1) :
    U ≤ ⨆ (E : Subgroup K) (_ : E ≤ U ∧ Nat.card E = p ^ 2 ∧ ∀ y ∈ E, y ^ p = 1), E := by
  intro x hx
  by_cases hx1 : x = 1
  · rw [hx1]
    exact one_mem _
  have hord : orderOf (⟨x, hx⟩ : U) = p := by
    apply orderOf_eq_prime
    · exact Subtype.ext (hexp x hx)
    · intro h
      exact hx1 (congrArg Subtype.val h)
  have hH : Nat.card (Subgroup.zpowers (⟨x, hx⟩ : U)) = p ^ 1 := by
    rw [Nat.card_zpowers, hord, pow_one]
  have hdvd : p ^ (1 + 1) ∣ Nat.card U := by
    rw [hcard]
    exact pow_dvd_pow p (by omega)
  obtain ⟨E', hE'card, hE'le⟩ := Sylow.exists_subgroup_card_pow_succ hdvd hH
  have hxE : x ∈ E'.map U.subtype := ⟨⟨x, hx⟩, hE'le (Subgroup.mem_zpowers _), rfl⟩
  refine Subgroup.mem_iSup_of_mem (E'.map U.subtype) (Subgroup.mem_iSup_of_mem ?_ hxE)
  exact ⟨Subgroup.map_subtype_le _,
    by rw [Subgroup.card_map_of_injective U.subtype_injective, hE'card],
    fun y hy => by
      obtain ⟨y', -, rfl⟩ := hy
      exact hexp y' y'.2⟩

end Elementary

section Torus

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

theorem pow_eq_one_of_torus (hp : p.Prime) {R : Subgroup X} (hcard : Nat.card R = p ^ 2) {t : X}
    (htN : t ∈ Subgroup.normalizer (R : Set X))
    (hline : ∀ Y₀ : Subgroup X, Y₀ ≤ R → Nat.card Y₀ = p →
      t ∉ Subgroup.normalizer (Y₀ : Set X)) :
    ∀ x ∈ R, x ^ p = 1 := by
  intro x hx
  by_contra hxp
  have hdvd : orderOf x ∣ p ^ 2 := hcard ▸ Subgroup.orderOf_dvd_natCard R hx
  obtain ⟨i, hi, hix⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hi2 : i = 2 := by
    by_contra hne
    apply hxp
    apply orderOf_dvd_iff_pow_eq_one.1
    rw [hix]
    calc p ^ i ∣ p ^ 1 := pow_dvd_pow p (by omega)
      _ = p := pow_one p
  subst hi2
  have hRx : Subgroup.zpowers x = R := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hx)
    rw [hcard, Nat.card_zpowers, hix]
  have hxpR : x ^ p ∈ R := R.pow_mem hx p
  have hord : orderOf (x ^ p) = p := by
    rw [orderOf_pow_of_dvd hp.ne_zero (by rw [hix]; exact dvd_pow_self p two_ne_zero), hix,
      pow_two, Nat.mul_div_cancel _ hp.pos]
  have hY₀R : Subgroup.zpowers (x ^ p) ≤ R := Subgroup.zpowers_le.2 hxpR
  have hY₀card : Nat.card (Subgroup.zpowers (x ^ p)) = p := by rw [Nat.card_zpowers, hord]
  refine hline _ hY₀R hY₀card ?_
  refine Subgroup.mem_normalizer_fintype fun y hy => ?_
  have hy' : y ∈ Subgroup.zpowers (x ^ p) := hy
  have hyR : y ∈ R := hY₀R hy'
  have hyp : y ^ p = 1 := by
    have h1 : orderOf y ∣ p := hY₀card ▸ Subgroup.orderOf_dvd_natCard _ hy'
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  have hzR : t * y * t⁻¹ ∈ R := (Subgroup.mem_normalizer_iff.1 htN y).1 hyR
  have hzp : (t * y * t⁻¹) ^ p = 1 := by rw [conj_pow, hyp]; group
  rw [← hRx] at hzR
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hzR
  rw [← hj] at hzp
  have h1 : x ^ (j * (p : ℤ)) = 1 := by rw [zpow_mul, zpow_natCast]; exact hzp
  have h2 := orderOf_dvd_iff_zpow_eq_one.2 h1
  rw [hix] at h2
  have h3 : (p : ℤ) ∣ j := by
    have h4 : (p : ℤ) * p ∣ j * p := by simpa [pow_two] using h2
    exact (mul_dvd_mul_iff_right (by exact_mod_cast hp.ne_zero)).1 h4
  obtain ⟨j', rfl⟩ := h3
  refine Subgroup.mem_zpowers_iff.2 ⟨j', ?_⟩
  rw [← hj, zpow_mul, zpow_natCast]

end Torus

section Criterion

private def fixedPts {K : Type} [Group K] (W : Subgroup (MulAut K)) : Subgroup K where
  carrier := {x | ∀ α ∈ W, α x = x}
  mul_mem' := fun {a b} ha hb α hα => by rw [map_mul, ha α hα, hb α hα]
  one_mem' := fun α _ => map_one α
  inv_mem' := fun {a} ha α hα => by rw [map_inv, ha α hα]

theorem signalizerTrivialOn_of_local {K : Type} [Group K] [Finite K] {p k : ℕ} (hp : p.Prime)
    (hk : 2 ≤ k) (hcen : Subgroup.center K = ⊥)
    (hsig : ∀ B Y : Subgroup (MulAut K), IsElemAbelian p B → Nat.card B = p ^ 2 →
      Nat.Coprime p (Nat.card Y) → B ≤ Subgroup.normalizer (Y : Set (MulAut K)) →
      B ≤ (MulAut.conj : K →* MulAut K).range → B ≤ Subgroup.centralizer (Y : Set (MulAut K)))
    (hP : ∀ P : Sylow p K, Nat.card (P : Subgroup K) = p ^ k ∧ ∀ x ∈ (P : Subgroup K), x ^ p = 1)
    (hA : ∀ R : Sylow p (MulAut K), Nat.card (R : Subgroup (MulAut K)) = p ^ k ∧
      Subgroup.centralizer (R : Set (MulAut K)) ≤ (R : Subgroup (MulAut K))) :
    SignalizerTrivialOn p K := by
  intro P W hW hnorm
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨hPcard, hPexp⟩ := hP P
  have hinj := injective_conj_of_center_eq_bot hcen
  have hplane : ∀ E : Subgroup K, E ≤ (P : Subgroup K) → Nat.card E = p ^ 2 →
      (∀ y ∈ E, y ^ p = 1) → ∀ w ∈ W, ∀ g ∈ E, w g = g := by
    intro E hEP hEcard hEexp w hw g hg
    have hBcomm : IsMulCommutative (E.map (MulAut.conj : K →* MulAut K)) := by
      haveI hE : IsMulCommutative E := IsPGroup.isMulCommutative_of_card_eq_prime_sq hEcard
      refine ⟨⟨fun a b => ?_⟩⟩
      obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.1 a.2
      obtain ⟨y, hy, hyb⟩ := Subgroup.mem_map.1 b.2
      apply Subtype.ext
      show (a : MulAut K) * b = b * a
      rw [← hxa, ← hyb, ← map_mul, ← map_mul]
      congr 1
      exact congrArg Subtype.val (hE.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    have hBel : IsElemAbelian p (E.map (MulAut.conj : K →* MulAut K)) := by
      refine ⟨hBcomm, fun x hx => ?_⟩
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
      rw [← map_pow, hEexp y hy, map_one]
    have hBN : E.map (MulAut.conj : K →* MulAut K) ≤ Subgroup.normalizer (W : Set (MulAut K)) := by
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro h
      refine ⟨fun hh => hnorm y (hEP hy) h hh, fun hh => ?_⟩
      have := hnorm y⁻¹ (inv_mem (hEP hy)) _ hh
      simpa [map_inv, mul_assoc] using this
    have hBc : E.map (MulAut.conj : K →* MulAut K) ≤ Subgroup.centralizer (W : Set (MulAut K)) :=
      hsig _ W hBel (by rw [Subgroup.card_map_of_injective hinj]; exact hEcard) hW hBN
        (Subgroup.map_le_range _ _)
    have hcomm : w * MulAut.conj g = MulAut.conj g * w :=
      Subgroup.mem_centralizer_iff.1 (hBc ⟨g, hg, rfl⟩) w hw
    apply hinj
    rw [← mulAut_mul_conj_mul_inv, hcomm]
    group
  have hgen := le_iSup_planes_of_card (p := p) (P : Subgroup K) hk hPcard hPexp
  have hfix : (P : Subgroup K) ≤ fixedPts W :=
    hgen.trans (iSup_le fun E => iSup_le fun hE => fun x hx α hα =>
      hplane E hE.1 hE.2.1 hE.2.2 α hα x hx)
  have hPφcard : Nat.card ((P : Subgroup K).map (MulAut.conj : K →* MulAut K)) = p ^ k := by
    rw [Subgroup.card_map_of_injective hinj]; exact hPcard
  obtain ⟨R, hR⟩ := (IsPGroup.of_card hPφcard).exists_le_sylow
  have hRcard := (hA R).1
  have hRP : (P : Subgroup K).map (MulAut.conj : K →* MulAut K) = (R : Subgroup (MulAut K)) :=
    Subgroup.eq_of_le_of_card_ge hR (by rw [hRcard, hPφcard])
  rw [eq_bot_iff]
  intro w hw
  rw [Subgroup.mem_bot]
  have hwC : w ∈ Subgroup.centralizer ((R : Subgroup (MulAut K)) : Set (MulAut K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    rw [← hRP] at hr
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hr
    have h1 := mulAut_mul_conj_mul_inv w g
    rw [hfix hg w hw] at h1
    show MulAut.conj g * w = w * MulAut.conj g
    rw [mul_inv_eq_iff_eq_mul] at h1
    exact h1.symm
  exact eq_one_of_mem_of_mem_of_coprime R.isPGroup' hW ((hA R).2 hwC) hw

end Criterion

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.SignalizerTrivial
