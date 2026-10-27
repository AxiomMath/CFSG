module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Input1433SameField
import CFSG.Adapters.StatedQuasisimple
import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6KL3U3Two

public section

namespace CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433

open CFSG.Open CFSG.Open.StatedCenterThree CFSG.LocalAnalysis.GLTheoremB
  CFSG.HardMathSupport.Solomon.LocalBalance Matrix
open CFSG.HardMathSupport.Solomon.Coordinator
  (HeisData heisR X_mem_heisR P_mem_heisR exists_heisData_statedSU_two)

private theorem scalar_mem_center {E : Type} [Field E] (H : Subgroup (GL (Fin 3) E)) (ω : Eˣ)
    (g : H) (hg : (g : GL (Fin 3) E) = Matrix.GeneralLinearGroup.scalar (Fin 3) ω) :
    g ∈ Subgroup.center H := by
  rw [Subgroup.mem_center_iff]
  intro h
  apply Subtype.ext
  show (h : GL (Fin 3) E) * (g : GL (Fin 3) E) = (g : GL (Fin 3) E) * (h : GL (Fin 3) E)
  rw [hg]
  exact (Matrix.GeneralLinearGroup.scalar_commute ω (h : GL (Fin 3) E)).symm

private theorem injective_of_card_center {Q J : Type} [Group Q] [Group J] [Finite Q]
    (φ : Q →* J) (hker : φ.ker ≤ Subgroup.center Q) (hZ : Nat.card (Subgroup.center Q) = 3)
    (g : Q) (hgc : g ∈ Subgroup.center Q) (hx : φ g ≠ 1) : Function.Injective φ := by
  rw [← MonoidHom.ker_eq_bot_iff]
  have hd : Nat.card φ.ker ∣ 3 := by
    have := Subgroup.card_dvd_of_le hker
    rwa [hZ] at this
  rcases (Nat.dvd_prime Nat.prime_three).1 hd with h1 | h1
  · exact Subgroup.eq_bot_of_card_eq _ h1
  · exfalso
    have heq : φ.ker = Subgroup.center Q :=
      Subgroup.eq_of_le_of_card_ge hker (by rw [hZ, h1])
    apply hx
    rw [← MonoidHom.mem_ker, heq]
    exact hgc

private theorem normal_eq_top_or_le_center {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q)
    {N : Subgroup Q} (hN : N.Normal) : N = ⊤ ∨ N ≤ Subgroup.center Q := by
  obtain ⟨hp', hs, -⟩ := hQ
  have hp : commutator Q = ⊤ := Group.isPerfect_def.1 hp'
  have := hN.map (QuotientGroup.mk' (Subgroup.center Q)) (QuotientGroup.mk'_surjective _)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (N.map (QuotientGroup.mk' (Subgroup.center Q))) with h | h
  · right
    rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h
  · left
    have hsup : N ⊔ Subgroup.center Q = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' (Subgroup.center Q)) N
      rw [h, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    have hZ : ⁅Subgroup.center Q, Subgroup.center Q⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.center_le_centralizer _)
    have hmap : (⊤ : Subgroup Q).map (QuotientGroup.mk' N) =
        (Subgroup.center Q).map (QuotientGroup.mk' N) := by
      rw [← hsup, Subgroup.map_sup, QuotientGroup.map_mk'_self, bot_sup_eq]
    have hcomm : commutator Q ≤ N := by
      rw [_root_.commutator_def, ← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator, hmap, ← Subgroup.map_commutator, hZ, Subgroup.map_bot]
    rw [hp] at hcomm
    exact eq_top_iff.mpr hcomm

private theorem eq_bot_of_quasisimple {Q : Type} [Group Q] [Finite Q]
    (hq : CFSG.IsQuasisimple Q) (h3 : 3 ∣ Nat.card Q) (hc : Nat.card (Subgroup.center Q) ∣ 27)
    {N : Subgroup Q} (hN : N.Normal) (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  rcases normal_eq_top_or_le_center hq hN with h | h
  · exfalso
    subst h
    rw [Subgroup.card_top] at hcop
    exact absurd (Nat.Coprime.eq_one_of_dvd hcop h3) (by norm_num)
  · have hd : Nat.card N ∣ 27 := (Subgroup.card_dvd_of_le h).trans hc
    have hcop27 : Nat.Coprime (Nat.card N) 27 := by
      rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
      exact Nat.Coprime.pow_right 3 hcop.symm
    exact Subgroup.eq_bot_of_card_eq N (Nat.Coprime.eq_one_of_dvd hcop27 hd)

private theorem normal_coprime_eq_bot_of_heis {Q : Type} [Group Q] [Finite Q] {X P w F : Q}
    (H : HeisData Q X P w F) {N : Subgroup Q} (hN : N.Normal)
    (hcop : Nat.Coprime 3 (Nat.card N)) : N = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hR : (heisR X P).Normal := H.normal_R
  have hR27 : Nat.card (heisR X P) = 27 := H.card_R
  have hcop27 : Nat.Coprime (Nat.card N) 27 := by
    rw [show (27 : ℕ) = 3 ^ 3 by norm_num]
    exact Nat.Coprime.pow_right 3 hcop.symm
  have hNR : N ⊓ heisR X P = ⊥ := by
    have hd1 : Nat.card ↥(N ⊓ heisR X P) ∣ Nat.card N := Subgroup.card_dvd_of_le inf_le_left
    have hd2 : Nat.card ↥(N ⊓ heisR X P) ∣ 27 := by
      have h := Subgroup.card_dvd_of_le (inf_le_right : N ⊓ heisR X P ≤ heisR X P)
      rwa [hR27] at h
    have hcopd : Nat.Coprime (Nat.card ↥(N ⊓ heisR X P)) 27 :=
      Nat.Coprime.coprime_dvd_left hd1 hcop27
    exact Subgroup.eq_bot_of_card_eq _ (Nat.Coprime.eq_one_of_dvd hcopd hd2)
  have hcomm : ∀ n ∈ N, ∀ x ∈ heisR X P, n * x = x * n := by
    intro n hn x hx
    have hc1 : n * x * n⁻¹ * x⁻¹ ∈ N := by
      have h1 : x * n⁻¹ * x⁻¹ ∈ N := hN.conj_mem n⁻¹ (N.inv_mem hn) x
      have h2 : n * x * n⁻¹ * x⁻¹ = n * (x * n⁻¹ * x⁻¹) := by simp only [mul_assoc]
      rw [h2]
      exact N.mul_mem hn h1
    have hc2 : n * x * n⁻¹ * x⁻¹ ∈ heisR X P := by
      have h1 : n * x * n⁻¹ ∈ heisR X P := hR.conj_mem x hx n
      exact (heisR X P).mul_mem h1 ((heisR X P).inv_mem hx)
    have hc3 : n * x * n⁻¹ * x⁻¹ ∈ N ⊓ heisR X P := ⟨hc1, hc2⟩
    rw [hNR, Subgroup.mem_bot] at hc3
    have h4 : n * x * n⁻¹ = x := mul_inv_eq_one.mp hc3
    exact mul_inv_eq_iff_eq_mul.mp h4
  have hone : ∀ n ∈ N, n = 1 := by
    intro n hn
    have hnX : n * X = X * n := hcomm n hn X (X_mem_heisR X P)
    have hnP : n * P = P * n := hcomm n hn P (P_mem_heisR X P)
    have hz : n ∈ Subgroup.center Q := H.cent n hnX hnP
    have hzw : n ∈ Subgroup.zpowers w := H.center_le n hz
    have hdvd3 : orderOf n ∣ 3 := by
      have h := orderOf_dvd_of_mem_zpowers hzw
      rwa [orderOf_eq_prime H.w_pow H.w_ne] at h
    have hdvdN : orderOf n ∣ Nat.card N := by
      rw [← Nat.card_zpowers n]
      exact Subgroup.card_dvd_of_le (Subgroup.zpowers_le.2 hn)
    have hcopn : Nat.Coprime (orderOf n) 3 := Nat.Coprime.coprime_dvd_left hdvdN hcop.symm
    exact orderOf_eq_one_iff.mp (Nat.Coprime.eq_one_of_dvd hcopn hdvd3)
  rw [eq_bot_iff]
  intro n hn
  rw [Subgroup.mem_bot]
  exact hone n hn

private theorem eq_bot_of_iso {Q J : Type} [Group Q] [Group J] [Finite Q] (e : Q ≃* J)
    (hP : ∀ N : Subgroup Q, N.Normal → Nat.Coprime 3 (Nat.card N) → N = ⊥) :
    ∀ N : Subgroup J, N.Normal → Nat.Coprime 3 (Nat.card N) → N = ⊥ := by
  intro N hNn hNc
  have hcard : Nat.card (N.comap e.toMonoidHom) = Nat.card N := by
    rw [Nat.card_congr (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective).toEquiv,
      Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N]
  have hbot : N.comap e.toMonoidHom = ⊥ := hP _ inferInstance (by rw [hcard]; exact hNc)
  rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective N, hbot,
    Subgroup.map_bot]

private theorem glaPPrimeCore_eq_bot_of_all {J : Type} [Group J]
    (hP : ∀ N : Subgroup J, N.Normal → Nat.Coprime 3 (Nat.card N) → N = ⊥) :
    GLAPPrimeCore 3 J = ⊥ := by
  refine eq_bot_iff.mpr (sSup_le fun N hN => ?_)
  obtain ⟨hNn, hNc⟩ := hN
  exact le_of_eq (hP N hNn hNc)


theorem isSL3EpsOver_of_statedSL_image {S : Type} [Group S] [Finite S] {J : Subgroup S}
    {E : Type} [Field E] [Finite E] (φ : ↥(StatedSL 3 E) →* ↥J) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center _) (ω : Eˣ) (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (g : ↥(StatedSL 3 E)) (hg : (g : GL (Fin 3) E) = Matrix.GeneralLinearGroup.scalar (Fin 3) ω)
    (hx : φ g ≠ 1) :
    Lemma27Ns.IsSL3EpsOver (↥J ⧸ GLAPPrimeCore 3 ↥J) (Nat.card E) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  have h3E : 3 ∣ Nat.card E - 1 := by
    rw [← Nat.card_units E, ← hord]
    exact orderOf_dvd_natCard ω
  have hZ : Nat.card (Subgroup.center ↥(StatedSL 3 E)) = 3 := card_center_statedSL_three h3E
  have hgc : g ∈ Subgroup.center ↥(StatedSL 3 E) := scalar_mem_center _ ω g hg
  have hinj : Function.Injective φ := injective_of_card_center φ hker hZ g hgc hx
  let e : ↥(StatedSL 3 E) ≃* ↥J := MulEquiv.ofBijective φ ⟨hinj, hφ⟩
  have hq : CFSG.IsQuasisimple ↥(StatedSL 3 E) :=
    CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) le_rfl E
  have h3 : 3 ∣ Nat.card ↥(StatedSL 3 E) := by
    have := Subgroup.card_subgroup_dvd_card (Subgroup.center ↥(StatedSL 3 E))
    rwa [hZ] at this
  have hP : ∀ N : Subgroup ↥(StatedSL 3 E), N.Normal → Nat.Coprime 3 (Nat.card N) → N = ⊥ :=
    fun N hN hcop => eq_bot_of_quasisimple hq h3 (by rw [hZ] <;> norm_num) hN hcop
  have hbot : GLAPPrimeCore 3 ↥J = ⊥ := glaPPrimeCore_eq_bot_of_all (eq_bot_of_iso e hP)
  let eY : (↥J ⧸ GLAPPrimeCore 3 ↥J) ≃* ↥(StatedSL 3 E) :=
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans e.symm
  unfold Lemma27Ns.IsSL3EpsOver
  refine ⟨Or.inl ⟨E, inferInstance, inferInstance, rfl, ⟨eY⟩⟩, ?_⟩
  rw [Nat.card_congr (Subgroup.centerCongr eY).toEquiv, hZ]

theorem isSL3EpsOver_of_statedSU_image {S : Type} [Group S] [Finite S] {J : Subgroup S}
    {E : Type} [Field E] [Finite E] {q : ℕ} (hE : Nat.card E = q ^ 2)
    (φ : ↥(StatedSU 3 q E) →* ↥J) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center _) (ω : Eˣ) (hω1 : ω ≠ 1) (hω3 : ω ^ 3 = 1)
    (g : ↥(StatedSU 3 q E)) (hg : (g : GL (Fin 3) E) = Matrix.GeneralLinearGroup.scalar (Fin 3) ω)
    (hx : φ g ≠ 1) :
    Lemma27Ns.IsSL3EpsOver (↥J ⧸ GLAPPrimeCore 3 ↥J) q := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf ω = 3 := orderOf_eq_prime hω3 hω1
  obtain ⟨p, f, hp, rfl⟩ : ∃ p f : ℕ, p.Prime ∧ q = p ^ f := by
    obtain ⟨p, hp⟩ := CharP.exists E
    letI : Fintype E := Fintype.ofFinite E
    obtain ⟨n, hpp, hn0⟩ := FiniteField.card E p
    have hn : Nat.card E = p ^ (n : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hn0
    have hqd : q ∣ p ^ (n : ℕ) := by
      rw [← hn, hE]
      exact Dvd.intro_left q (sq q).symm
    obtain ⟨f, -, hf⟩ := (Nat.dvd_prime_pow hpp).1 hqd
    exact ⟨p, f, hpp, hf⟩
  haveI : Fact p.Prime := ⟨hp⟩
  have hω_mem : Matrix.GeneralLinearGroup.scalar (Fin 3) ω ∈ StatedSU 3 (p ^ f) E :=
    hg ▸ g.2
  have hωq : ω ^ (p ^ f + 1) = 1 :=
    (((CFSG.LinearGroups.unitary_scalar_kernel hp hE (by norm_num : 1 ≤ 3)).2.1 ω).mp hω_mem).2
  have h3q : 3 ∣ p ^ f + 1 := by
    rw [← hord]
    exact orderOf_dvd_of_pow_eq_one hωq
  have hZ : Nat.card (Subgroup.center ↥(StatedSU 3 (p ^ f) E)) = 3 :=
    card_center_statedSU_three hE h3q
  have hgc : g ∈ Subgroup.center ↥(StatedSU 3 (p ^ f) E) := scalar_mem_center _ ω g hg
  have hinj : Function.Injective φ := injective_of_card_center φ hker hZ g hgc hx
  let e : ↥(StatedSU 3 (p ^ f) E) ≃* ↥J := MulEquiv.ofBijective φ ⟨hinj, hφ⟩
  have hP : ∀ N : Subgroup ↥(StatedSU 3 (p ^ f) E), N.Normal →
      Nat.Coprime 3 (Nat.card N) → N = ⊥ := by
    by_cases h2 : p ^ f = 2
    ·
      have hK : Nat.card E = (2 ^ 1) ^ 2 := by rw [hE, h2] <;> norm_num
      obtain ⟨X, P, w, F, H, -⟩ := exists_heisData_statedSU_two hK
      have h21 : (2 ^ 1 : ℕ) = p ^ f := by rw [h2] <;> norm_num
      let e0 : ↥(StatedSU 3 (2 ^ 1) E) ≃* ↥(StatedSU 3 (p ^ f) E) :=
        MulEquiv.subgroupCongr (congrArg (fun m : ℕ => StatedSU 3 m E) h21)
      exact eq_bot_of_iso e0 (fun N hN hcop => normal_coprime_eq_bot_of_heis H hN hcop)
    · have hnq : (3, p ^ f) ≠ (3, 2) := fun h => h2 (Prod.mk.inj h).2
      have hq : CFSG.IsQuasisimple ↥(StatedSU 3 (p ^ f) E) :=
        (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hE (le_refl 3) hnq).1
      have h3 : 3 ∣ Nat.card ↥(StatedSU 3 (p ^ f) E) := by
        have := Subgroup.card_subgroup_dvd_card (Subgroup.center ↥(StatedSU 3 (p ^ f) E))
        rwa [hZ] at this
      exact fun N hN hcop => eq_bot_of_quasisimple hq h3 (by rw [hZ] <;> norm_num) hN hcop
  have hbot : GLAPPrimeCore 3 ↥J = ⊥ := glaPPrimeCore_eq_bot_of_all (eq_bot_of_iso e hP)
  let eY : (↥J ⧸ GLAPPrimeCore 3 ↥J) ≃* ↥(StatedSU 3 (p ^ f) E) :=
    ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot).trans e.symm
  unfold Lemma27Ns.IsSL3EpsOver
  refine ⟨Or.inr ⟨E, inferInstance, inferInstance, hE, ⟨eY⟩⟩, ?_⟩
  rw [Nat.card_congr (Subgroup.centerCongr eY).toEquiv, hZ]

end CFSG.HardMathSupport.Solomon.LocalBalance.Lemma27Ns.I1433
