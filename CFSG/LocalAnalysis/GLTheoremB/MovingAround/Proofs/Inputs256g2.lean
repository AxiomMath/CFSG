module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs256g

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256g

open CFSG.Open CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs2311c (UniPlaneGen uniPlaneClosure
  mem_uniPlaneClosure)

theorem uniPlaneGen_of_eq {S : Type*} [Group S] {r r' : ℕ} (hr : r = r') {E : Subgroup (MulAut S)}
    (hE : UniPlaneGen r E) : UniPlaneGen r' E := hr ▸ hE

section Heis5

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

variable {ℓ f n : ℕ} {K : Type} [Field K]

theorem lifts_commute_of_commute_u (h : UnitaryFieldData ℓ f K) (hn : 3 ≤ n)
    {E : Subgroup (MulAut (primeFormP h (idGram K n)))} {X Y : primeFormUnitary h (idGram K n)}
    (hgen : Subgroup.zpowers (primeFormConjHom h (idGram K n) X) ⊔
      Subgroup.zpowers (primeFormConjHom h (idGram K n) Y) = E) (hXY : X * Y = Y * X)
    {A B : primeFormUnitary h (idGram K n)} (hA : primeFormConjHom h (idGram K n) A ∈ E)
    (hB : primeFormConjHom h (idGram K n) B ∈ E) : A * B = B * A := by
  have hcent : ∀ g : primeFormUnitary h (idGram K n), primeFormConjHom h (idGram K n) g = 1 →
      ∀ z : primeFormUnitary h (idGram K n), z * g = g * z := by
    intro g hg z
    obtain ⟨u, -, hu⟩ := eq_scalar_of_conj_eq_one h hn g hg
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, hu]
    exact (commute_scalar u (z : GL (Fin n) K)).eq
  set C := Subgroup.centralizer ({X, Y} : Set (primeFormUnitary h (idGram K n))) with hC
  have hXC : X ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    rintro z (rfl | rfl)
    · rfl
    · exact hXY.symm
  have hYC : Y ∈ C := by
    rw [Subgroup.mem_centralizer_iff]
    rintro z (rfl | rfl)
    · exact hXY
    · rfl
  have hkC : ∀ g, primeFormConjHom h (idGram K n) g = 1 → g ∈ C := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro z _
    exact hcent g hg z
  have hBC : B ∈ C := mem_of_conj_mem_of_sup_eq h hgen hkC hXC hYC hB
  set C' := Subgroup.centralizer (C : Set (primeFormUnitary h (idGram K n))) with hC'
  have hXC' : X ∈ C' := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.1 hz) X (Set.mem_insert X _)).symm
  have hYC' : Y ∈ C' := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.1 hz) Y (Set.mem_insert_of_mem X rfl)).symm
  have hkC' : ∀ g, primeFormConjHom h (idGram K n) g = 1 → g ∈ C' := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro z _
    exact hcent g hg z
  have hAC' : A ∈ C' := mem_of_conj_mem_of_sup_eq h hgen hkC' hXC' hYC' hA
  exact ((Subgroup.mem_centralizer_iff.1 hAC') B hBC).symm

variable [Finite K] [Fact ℓ.Prime] [CharP K ℓ]

theorem heis_fixed_five_eq_one_u (h : UnitaryFieldData ℓ f K) (h5 : ℓ = 5)
    {E : Subgroup (MulAut (primeFormP h (idGram K 3)))} (hE : IsElemAbelian 3 E)
    (hc : Nat.card E = 3 ^ 2) (hD : E ≤ primeFormD h (idGram K 3))
    (hnonab : ∃ A B : primeFormUnitary h (idGram K 3), primeFormConjHom h (idGram K 3) A ∈ E ∧
      primeFormConjHom h (idGram K 3) B ∈ E ∧ A * B ≠ B * A)
    {e₀ : MulAut (primeFormP h (idGram K 3))} (he₀ : e₀ ∈ E) (he₀1 : e₀ ≠ 1)
    {s : primeFormP h (idGram K 3)} (hs : e₀ s = s) (hs5 : s ^ 5 = 1) : s = 1 := by
  classical
  subst h5
  have hn : 3 ≤ 3 := le_rfl
  obtain ⟨e'', he''E, he''⟩ := exists_notMem_zpowers_of_card_sq Nat.prime_three hE.2 hc he₀ he₀1
  have hgen := zpowers_sup_zpowers_eq_of_card_sq Nat.prime_three hE.2 hc he₀ he₀1 he''E he''
  obtain ⟨X, rfl⟩ := hD he₀
  obtain ⟨B, rfl⟩ := hD he''E
  have hncomm : X * B ≠ B * X := by
    intro hXB
    obtain ⟨A₁, A₂, hA₁, hA₂, hA⟩ := hnonab
    exact hA (lifts_commute_of_commute_u h hn hgen hXB hA₁ hA₂)
  have hcomm : primeFormConjHom h (idGram K 3) X * primeFormConjHom h (idGram K 3) B =
      primeFormConjHom h (idGram K 3) B * primeFormConjHom h (idGram K 3) X :=
    congrArg Subtype.val (hE.1.is_comm.comm ⟨_, he₀⟩ ⟨_, he''E⟩)
  obtain ⟨c, hcBX⟩ := exists_smul_comm_of_conj h hn X B hcomm
  obtain ⟨α, hα, hXp⟩ := exists_pow_eq_smul_of_conj h hn X (hE.2 _ he₀)
  have hc3 : c ^ 3 = 1 := pow_eq_one_of_smul_comm_p (by norm_num) hα hXp hcBX
  have hc1 : c ≠ 1 := by
    rintro rfl
    apply hncomm
    apply Subtype.ext
    apply Units.ext
    simp only [Subgroup.coe_mul, Units.val_mul]
    rw [hcBX, one_smul]
  obtain ⟨k₀, rfl⟩ := QuotientGroup.mk_surjective s
  have hk₀5 : k₀ ^ 5 ∈ normOneScalars h (gramSU h (idGram K 3)) 3 := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]; exact hs5
  obtain ⟨z, -, hz3, hz⟩ := hk₀5
  have hk₀15 : k₀ ^ 15 = 1 := by
    apply Subtype.ext
    rw [show (15 : ℕ) = 5 * 3 from rfl, pow_mul, SubgroupClass.coe_pow, hz, ← map_pow, hz3,
      map_one, OneMemClass.coe_one]
  set k := k₀ ^ 6 with hkdef
  have hk5 : k ^ 5 = 1 := by
    rw [hkdef, ← pow_mul, show 6 * 5 = 15 * 2 from rfl, pow_mul, hk₀15, one_pow]
  have hks : (k : primeFormP h (idGram K 3)) = (k₀ : primeFormP h (idGram K 3)) := by
    rw [hkdef, QuotientGroup.mk_pow, show (6 : ℕ) = 5 + 1 from rfl, pow_succ, hs5, one_mul]
  have hfix : primeFormConjHom h (idGram K 3) X (k : primeFormP h (idGram K 3)) =
      (k : primeFormP h (idGram K 3)) := by rw [hks]; exact hs
  rw [primeFormConjHom_mk] at hfix
  obtain ⟨w, -, hw3, hw⟩ := QuotientGroup.eq.1 hfix
  set kG : GL (Fin 3) K := (k : GL (Fin 3) K) with hkG
  have hkG5 : kG ^ 5 = 1 := by
    rw [hkG, ← SubgroupClass.coe_pow, hk5, OneMemClass.coe_one]
  have hrel : ((X : GL (Fin 3) K) * kG * (X : GL (Fin 3) K)⁻¹)⁻¹ * kG =
      Matrix.GeneralLinearGroup.scalar (Fin 3) w := by
    rw [← hw]; rfl
  have hk' : kG = ((X : GL (Fin 3) K) * kG * (X : GL (Fin 3) K)⁻¹) *
      Matrix.GeneralLinearGroup.scalar (Fin 3) w := by
    rw [← hrel]; group
  have hw5 : w ^ 5 = 1 := by
    have h1 : kG ^ 5 = ((X : GL (Fin 3) K) * kG * (X : GL (Fin 3) K)⁻¹) ^ 5 *
        Matrix.GeneralLinearGroup.scalar (Fin 3) (w ^ 5) := by
      conv_lhs => rw [hk']
      rw [(commute_scalar w ((X : GL (Fin 3) K) * kG * (X : GL (Fin 3) K)⁻¹)).mul_pow, map_pow]
    have h2 : ((X : GL (Fin 3) K) * kG * (X : GL (Fin 3) K)⁻¹) ^ 5 = 1 := by
      rw [conj_pow, hkG5]; group
    rw [hkG5, h2, one_mul] at h1
    have h3 : (w : K) ^ 5 = 1 := by
      have h4 := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) h1
      simp only [Units.val_one, Matrix.one_apply_eq, coe_scalar_gl, Matrix.smul_apply, smul_eq_mul,
        mul_one] at h4
      simpa using h4.symm
    exact Units.ext (by rw [Units.val_pow_eq_pow_val, h3, Units.val_one])
  have hw1 : w = 1 := by
    have := (pow_gcd_eq_one (a := w) (m := 5) (n := 3)).2 ⟨hw5, hw3⟩
    rwa [show Nat.gcd 5 3 = 1 by norm_num, pow_one] at this
  have hkX : (kG : Matrix (Fin 3) (Fin 3) K) * ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * kG := by
    rw [hw1, map_one, mul_one] at hk'
    have h1 : kG * (X : GL (Fin 3) K) = (X : GL (Fin 3) K) * kG := by
      conv_lhs => rw [hk']
      group
    rw [← Units.val_mul, ← Units.val_mul, h1]
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set Nm : Matrix (Fin 3) (Fin 3) K := (kG : Matrix (Fin 3) (Fin 3) K) - 1 with hNm
  have hN5 : Nm ^ 5 = 0 := by
    rw [hNm, sub_pow_char_of_commute (R := Matrix (Fin 3) (Fin 3) K) (p := 5)
      (x := (kG : Matrix (Fin 3) (Fin 3) K)) (y := 1) (Commute.one_right _), one_pow,
      ← Units.val_pow_eq_pow_val, hkG5, Units.val_one, sub_self]
  have hNX : Nm * ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((X : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * Nm := by
    rw [hNm, Matrix.sub_mul, Matrix.mul_sub, hkX, Matrix.one_mul, Matrix.mul_one]
  have hcF1 : c ≠ 1 := hc1
  have hN0 := Inputs256e.heis_nilpotent_eq_zero (X : GL (Fin 3) K).isUnit (B : GL (Fin 3) K).isUnit
    hcBX hcF1 hc3 hN5 hNX
  have hk1 : k = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [OneMemClass.coe_one, Units.val_one]
    exact sub_eq_zero.1 hN0
  rw [← hks, hk1, QuotientGroup.mk_one]

end Heis5

section Five

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel

theorem uniGenFiveNonCpfUnitary_holds :
    Inputs256e.UniGenFiveNonCpfUnitary := by
  rintro ⟨d, hv⟩ ⟨m, q, rfl⟩ hd5 hcpf E hE hc hfive
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  have hq5 : q.p = 5 := by simpa using hd5
  simp only [CentralPrimeFree, not_not] at hcpf
  obtain ⟨h3q, h3m⟩ := hcpf
  obtain ⟨⟨hℓ, hf, hn3, -⟩, F, _, _, hKF, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m q hv
      (MulEquiv.refl (Cat ⟨.twistedA m q, hv⟩))
  have h : UnitaryFieldData q.p q.exponent F := ⟨hℓ, hf, by rw [hKF, ← pow_mul, mul_comm]⟩
  haveI : Finite F := h.finite
  haveI : CharP F q.p := h.charP
  have hn1 : 1 ≤ m + 1 := by omega
  set e : Cat ⟨.twistedA m q, hv⟩ ≃* primeFormP h (idGram F (m + 1)) :=
    eT.trans (BalanceLp.statedProjEquivPrimeFormP h hn1) with he
  set E' := E.map (MulAut.congr e).toMonoidHom with hE'
  suffices hU : UniPlaneGen 5 E' from (Inputs2311c.uniPlaneGen_map_congr e 5 E).1 hU
  have hE'el : IsElemAbelian 3 E' := CFSG.Open.IsElemAbelian.map hE _
  have hE'c : Nat.card E' = 3 ^ 2 := by
    rw [hE', Subgroup.card_map_of_injective (MulAut.congr e).injective, hc]
  have hpq : 3 ∣ q.p ^ q.exponent + 1 := by rw [← TauCeti.PrimePower.card_def]; exact h3q
  rcases uniPlaneGen_psu h (by rw [hq5]; norm_num) hn3 Nat.prime_three (by norm_num)
      (by rw [hq5]; norm_num) hpq hE'el hE'c with hU | ⟨hD, hnp, hnonab⟩
  · exact uniPlaneGen_of_eq hq5 hU
  · exfalso
    obtain ⟨e₀, he₀, he₀1, s, hs1, hs, hs5⟩ := hfive
    have hm : m = 2 := by omega
    subst hm
    have he₀' : MulAut.congr e e₀ ∈ E' := Subgroup.mem_map_of_mem _ he₀
    have he₀1' : MulAut.congr e e₀ ≠ 1 := fun h1 =>
      he₀1 ((MulAut.congr e).injective (by rw [h1, map_one]))
    have hs' : MulAut.congr e e₀ (e s) = e s := by simp [MulAut.congr_apply, hs]
    have hs5' : (e s) ^ 5 = 1 := by rw [← map_pow, hs5, map_one]
    have h1 := heis_fixed_five_eq_one_u h hq5 hE'el hE'c hD hnonab he₀' he₀1' hs' hs5'
    exact hs1 (e.injective (by rw [h1, map_one]))

end Five

section Thm4

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.LocalAnalysis.GLTheoremB
open CFSG.HardMathSupport.Solomon.LocalBalance (barOf barAut autBar)

variable {G : Type} [Group G] [Finite G]

theorem thm4RestUnitary_holds : Inputs256e.Thm4RestUnitary := by
  intro G _ _ p q hp hp2 hq hq2 hqp a K E A hK hmod hA0C hA0el hA0r hN hF hIii
  obtain ⟨m, Q, hv, hQq, hncpf, ⟨θ⟩⟩ := hmod
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact Q.p.Prime := ⟨Q.prime_p⟩
  subst hQq
  set A0 := E ⊓ A with hA0
  set N : Subgroup G := Subgroup.normalizer (K : Set G) with hNdef
  obtain ⟨⟨hℓ, hf, hn3, -⟩, F, _, _, hKF, ⟨eT⟩⟩ :=
    CFSG.QuasithinUnique.SQTK.statedClassicalModel_twistedA m Q hv
      (MulEquiv.refl (Cat ⟨.twistedA m Q, hv⟩))
  have h : UnitaryFieldData Q.p Q.exponent F := ⟨hℓ, hf, by rw [hKF, ← pow_mul, mul_comm]⟩
  haveI : Finite F := h.finite
  haveI : CharP F Q.p := h.charP
  have hn1 : 1 ≤ m + 1 := by omega
  let e : Cat ⟨.twistedA m Q, hv⟩ ≃* primeFormP h (idGram F (m + 1)) :=
    eT.trans (BalanceLp.statedProjEquivPrimeFormP h hn1)
  set ψ : ↥N →* MulAut (primeFormP h (idGram F (m + 1))) :=
    (MulAut.congr e).toMonoidHom.comp (Inputs2311c.catAct θ) with hψ
  simp only [CentralPrimeFree, not_not] at hncpf
  obtain ⟨hpQ, hpm⟩ := hncpf
  have hpq' : p ∣ Q.p ^ Q.exponent + 1 := by rw [← TauCeti.PrimePower.card_def]; exact hpQ
  have hℓ2 : Q.p ≠ 2 := hq2
  have hpℓ : p ≠ Q.p := Ne.symm hqp
  suffices hD : ∃ D : Subgroup G, D ≤ A0 ∧ UniPlaneGen Q.p ((D.subgroupOf N).map ψ) by
    obtain ⟨D, hDA, hgen⟩ := hD
    have hgen' : UniPlaneGen Q.p ((D.subgroupOf N).map (Inputs2311c.catAct θ)) := by
      have h1 : (D.subgroupOf N).map ψ =
          ((D.subgroupOf N).map (Inputs2311c.catAct θ)).map (MulAut.congr e).toMonoidHom := by
        rw [hψ, Subgroup.map_map]
      rw [h1] at hgen
      exact (Inputs2311c.uniPlaneGen_map_congr e Q.p _).1 hgen
    exact Inputs2311c.le_iSup_of_uniPlaneGen hp hq hqp hK θ hA0C hN hDA hgen'
  have hψ1 : ∀ x : ↥N, (x : G) ∈ A0 → ψ x = 1 → (x : G) = 1 := fun x hx h1 =>
    Inputs256e.catAct_eq_one hp hK θ hF hx ((MulAut.congr e).map_eq_one_iff.1 h1)
  have hA0comm : ∀ x ∈ A0, ∀ y ∈ A0, Commute x y := fun x hx y hy =>
    congrArg Subtype.val (hA0el.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hplane : ∀ x : ↥N, (x : G) ∈ A0 → (x : G) ≠ 1 → ∀ y : ↥N, (y : G) ∈ A0 →
      (y : G) ∉ Subgroup.zpowers (x : G) →
      Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G) ≤ A0 ∧
        IsElemAbelian p (((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ) ∧
        Nat.card (((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ) = p ^ 2 ∧
        Subgroup.zpowers (ψ x) ⊔ Subgroup.zpowers (ψ y) =
          ((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ := by
    intro x hx hx1 y hy hyx
    set D := Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G) with hDdef
    have hDA : D ≤ A0 := sup_le (Subgroup.zpowers_le.2 hx) (Subgroup.zpowers_le.2 hy)
    obtain ⟨hDel, hDc⟩ := Inputs256e.sup_zpowers_facts hp (hA0comm _ hx _ hy) (hA0el.2 _ hx)
      (hA0el.2 _ hy) hx1 hyx
    obtain ⟨hE1, hEc⟩ := Inputs2311c.catAct_plane hp hK θ hN hF hDA hDel hDc
    have hEel : IsElemAbelian p ((D.subgroupOf N).map ψ) := by
      rw [hψ, ← Subgroup.map_map]
      exact CFSG.Open.IsElemAbelian.map hE1 _
    have hEcard : Nat.card ((D.subgroupOf N).map ψ) = p ^ 2 := by
      rw [hψ, ← Subgroup.map_map, Subgroup.card_map_of_injective (MulAut.congr e).injective, hEc]
    have hxD : x ∈ D.subgroupOf N :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    have hyD : y ∈ D.subgroupOf N :=
      Subgroup.mem_subgroupOf.2 (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
    have hψx1 : ψ x ≠ 1 := fun h' => hx1 (hψ1 x hx h')
    have hψyx : ψ y ∉ Subgroup.zpowers (ψ x) := by
      intro hmemz
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hmemz
      apply hyx
      have h1 : ψ (y * (x ^ k)⁻¹) = 1 := by
        rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
      have hmem : ((y * (x ^ k)⁻¹ : ↥N) : G) ∈ A0 := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
        exact A0.mul_mem hy (A0.inv_mem (A0.zpow_mem hx k))
      have h2 := hψ1 _ hmem h1
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow] at h2
      exact ⟨k, (mul_inv_eq_one.1 h2).symm⟩
    refine ⟨hDA, hEel, hEcard, ?_⟩
    exact zpowers_sup_zpowers_eq_of_card_sq hp hEel.2 hEcard (Subgroup.mem_map_of_mem _ hxD) hψx1
      (Subgroup.mem_map_of_mem _ hyD) hψyx
  have hmodel : ∀ x : ↥N, (x : G) ∈ A0 → (x : G) ≠ 1 → ∀ y : ↥N, (y : G) ∈ A0 →
      (y : G) ∉ Subgroup.zpowers (x : G) →
      UniPlaneGen Q.p (((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ) ∨
        ((((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ ≤
            primeFormD h (idGram F (m + 1))) ∧ m + 1 = p ∧
          ∃ A' B' : primeFormUnitary h (idGram F (m + 1)),
            primeFormConjHom h (idGram F (m + 1)) A' ∈
              ((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ ∧
            primeFormConjHom h (idGram F (m + 1)) B' ∈
              ((Subgroup.zpowers (x : G) ⊔ Subgroup.zpowers (y : G)).subgroupOf N).map ψ ∧
            A' * B' ≠ B' * A') := by
    intro x hx hx1 y hy hyx
    obtain ⟨-, hEel, hEcard, -⟩ := hplane x hx hx1 y hy hyx
    exact uniPlaneGen_psu h hℓ2 hn3 hp hp2 hpℓ hpq' hEel hEcard
  have hcommPlane : ∀ x : ↥N, (x : G) ∈ A0 → (x : G) ≠ 1 → ∀ y : ↥N, (y : G) ∈ A0 →
      (y : G) ∉ Subgroup.zpowers (x : G) → ∀ X Y : primeFormUnitary h (idGram F (m + 1)),
      primeFormConjHom h (idGram F (m + 1)) X = ψ x →
      primeFormConjHom h (idGram F (m + 1)) Y = ψ y → X * Y = Y * X →
      ∃ D : Subgroup G, D ≤ A0 ∧ UniPlaneGen Q.p ((D.subgroupOf N).map ψ) := by
    intro x hx hx1 y hy hyx X Y hX hY hXY
    obtain ⟨hDA, -, -, hgen⟩ := hplane x hx hx1 y hy hyx
    rcases hmodel x hx hx1 y hy hyx with h' | ⟨-, -, A', B', hA', hB', hAB'⟩
    · exact ⟨_, hDA, h'⟩
    · rw [← hX, ← hY] at hgen
      exact absurd (lifts_commute_of_commute_u h hn3 hgen hXY hA' hB') hAB'
  have hA0card : p ^ 2 ≤ Nat.card A0 := by
    obtain ⟨D₀, hD₀A, -, hD₀c⟩ := CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank hA0r
    rw [← hD₀c]
    exact Subgroup.card_le_of_le hD₀A
  have hindep : ∀ x ∈ A0, ∃ y ∈ A0, y ∉ Subgroup.zpowers x := by
    intro x hx
    by_contra hcon
    push Not at hcon
    have hle : A0 ≤ Subgroup.zpowers x := hcon
    have h1 := Subgroup.card_le_of_le hle
    have h2 : Nat.card (Subgroup.zpowers x) ≤ p := by
      rw [Nat.card_zpowers]
      exact Nat.le_of_dvd hp.pos (orderOf_dvd_of_pow_eq_one (hA0el.2 x hx))
    have : p ^ 2 ≤ p := hA0card.trans (h1.trans h2)
    nlinarith [hp.two_le]
  obtain ⟨x₀, hx₀A, hx₀1⟩ : ∃ x ∈ A0, x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : A0 = ⊥ := (Subgroup.eq_bot_iff_forall A0).2 hcon
    rw [this, Subgroup.card_bot] at hA0card
    nlinarith [hp.two_le]
  by_cases hout : ∃ x : ↥N, (x : G) ∈ A0 ∧ ψ x ∉ primeFormD h (idGram F (m + 1))
  · obtain ⟨x, hx, hxl⟩ := hout
    have hx1 : (x : G) ≠ 1 := fun h' => hxl (by
      rw [show x = 1 from Subtype.ext h', map_one]; exact one_mem _)
    obtain ⟨y, hy, hyx⟩ := hindep _ hx
    set y' : ↥N := ⟨y, hN hy⟩
    obtain ⟨hDA, -, -, hgen⟩ := hplane x hx hx1 y' hy hyx
    rcases hmodel x hx hx1 y' hy hyx with h' | ⟨hle, -⟩
    · exact ⟨_, hDA, h'⟩
    · exact absurd (hle (hgen ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers _))) hxl
  push Not at hout
  set x' : ↥N := ⟨x₀, hN hx₀A⟩ with hx'
  obtain ⟨y₀, hy₀A, hy₀x⟩ := hindep _ hx₀A
  set y' : ↥N := ⟨y₀, hN hy₀A⟩ with hy'
  obtain ⟨X, hX⟩ := hout x' hx₀A
  obtain ⟨Y, hY⟩ := hout y' hy₀A
  by_cases hXY : X * Y = Y * X
  · exact hcommPlane x' hx₀A hx₀1 y' hy₀A hy₀x X Y hX hY hXY
  obtain ⟨hD₁A, hE₁el, hE₁c, hgen₁⟩ := hplane x' hx₀A hx₀1 y' hy₀A hy₀x
  by_cases hcard : Nat.card A0 = p ^ 2
  ·
    have hD₁eq : Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ = A0 :=
      Subgroup.eq_of_le_of_card_ge hD₁A (by
        rw [hcard, (Inputs256e.sup_zpowers_facts hp (hA0comm _ hx₀A _ hy₀A) (hA0el.2 _ hx₀A)
          (hA0el.2 _ hy₀A) hx₀1 hy₀x).2])
    rcases hmodel x' hx₀A hx₀1 y' hy₀A hy₀x with h' | ⟨hle, hmp, A', B', hA', hB', hAB'⟩
    · exact ⟨_, hD₁A, h'⟩
    exfalso
    apply hIii
    subst hmp
    let θ'' : barOf (m + 1) K ⧸ Subgroup.center (barOf (m + 1) K) ≃*
        StatedProj (StatedSU (m + 1) (Q.p ^ Q.exponent) F) := θ.trans eT
    have hBmap : (autBar (m + 1) A0 K).map
        (BalanceLp.modelHom (θ''.trans (BalanceLp.statedProjEquivPrimeFormP h hn1))) =
          ((Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀).subgroupOf N).map ψ := by
      rw [hD₁eq, autBar, Subgroup.map_map, inf_eq_left.2 hN]
      congr 1
    have hDp : IsPGroup (m + 1) ((autBar (m + 1) A0 K).map
        (BalanceLp.modelHom (θ''.trans (BalanceLp.statedProjEquivPrimeFormP h hn1)))) := by
      rw [hBmap]
      exact CFSG.Open.IsElemAbelian.isPGroup hE₁el
    have hDr : (autBar (m + 1) A0 K).map
        (BalanceLp.modelHom (θ''.trans (BalanceLp.statedProjEquivPrimeFormP h hn1))) ≤
          (primeFormConjHom h (idGram F (m + 1))).range := by
      rw [hBmap]
      exact hle
    obtain ⟨P, hP, hPD, hDP⟩ :=
      BalanceLp.exists_pGroup_image (primeFormConjHom h (idGram F (m + 1))) hDp hDr
    have hnab : ∃ x ∈ P.map (primeFormUnitary h (idGram F (m + 1))).subtype,
        ∃ y ∈ P.map (primeFormUnitary h (idGram F (m + 1))).subtype, x * y ≠ y * x := by
      obtain ⟨x'', hx''P, hx''⟩ := hDP _ (by rw [hBmap]; exact hA')
      obtain ⟨y'', hy''P, hy''⟩ := hDP _ (by rw [hBmap]; exact hB')
      refine ⟨x'', ⟨x'', hx''P, rfl⟩, y'', ⟨y'', hy''P, rfl⟩, fun hxy => hAB' ?_⟩
      obtain ⟨c, -, hc⟩ := eq_scalar_of_conj_eq_one h hn3 (A'⁻¹ * x'')
        (by rw [map_mul, map_inv, hx'', inv_mul_cancel])
      obtain ⟨d, -, hd⟩ := eq_scalar_of_conj_eq_one h hn3 (B'⁻¹ * y'')
        (by rw [map_mul, map_inv, hy'', inv_mul_cancel])
      have hx''e : (x'' : GL (Fin (m + 1)) F) =
          (A' : GL (Fin (m + 1)) F) * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) c := by
        rw [← hc]; simp
      have hy''e : (y'' : GL (Fin (m + 1)) F) =
          (B' : GL (Fin (m + 1)) F) * Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) d := by
        rw [← hd]; simp
      have hxy' : (x'' : GL (Fin (m + 1)) F) * y'' = y'' * x'' := hxy
      rw [hx''e, hy''e] at hxy'
      apply Subtype.ext
      exact BalanceLp.mul_comm_of_central (fun g => (commute_scalar c g).eq.symm)
        (fun g => (commute_scalar d g).eq.symm) hxy'
    have hFq : Nat.card F = (Q.p ^ Q.exponent) ^ 2 := hKF
    refine ⟨⟨Q.exponent, Or.inr ⟨⟨F, inferInstance, inferInstance, hFq, ⟨θ''⟩⟩, hpq',
      F, inferInstance, inferInstance, θ'', hFq, P.map (primeFormUnitary h (idGram F (m + 1))).subtype,
      ?_, hP.map _, hnab, fun b hb => ?_, ?_⟩⟩, hN, hcard, hF⟩
    · rintro _ ⟨g, -, rfl⟩
      exact BalanceLp.primeFormUnitary_le_GUn h (m + 1) g.2
    · obtain ⟨g, hgP, hg⟩ := hDP _ ⟨b, hb, rfl⟩
      exact ⟨g, ⟨g, hgP, rfl⟩, BalanceLp.actsAsConj_unitary h hn1 θ'' b g hg.symm⟩
    · rintro _ ⟨g, hgP, rfl⟩
      obtain ⟨b, hb, hbg⟩ := hPD g hgP
      exact ⟨b, hb, BalanceLp.actsAsConj_unitary h hn1 θ'' b g hbg⟩
  ·
    have hD₁c : Nat.card ↥(Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀) = p ^ 2 :=
      (Inputs256e.sup_zpowers_facts hp (hA0comm _ hx₀A _ hy₀A) (hA0el.2 _ hx₀A) (hA0el.2 _ hy₀A)
        hx₀1 hy₀x).2
    obtain ⟨z₀, hz₀A, hz₀D⟩ : ∃ z ∈ A0, z ∉ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ := by
      by_contra hcon
      push Not at hcon
      have hle : A0 ≤ Subgroup.zpowers x₀ ⊔ Subgroup.zpowers y₀ := hcon
      exact hcard (le_antisymm (hD₁c ▸ Subgroup.card_le_of_le hle) hA0card)
    set z' : ↥N := ⟨z₀, hN hz₀A⟩ with hz'
    obtain ⟨Z, hZ⟩ := hout z' hz₀A
    have hĀel : IsElemAbelian p ((A0.subgroupOf N).map ψ) :=
      CFSG.Open.IsElemAbelian.map (l119_isElemAbelian_subgroupOf hA0el N) _
    have hXĀ : primeFormConjHom h (idGram F (m + 1)) X ∈ (A0.subgroupOf N).map ψ :=
      hX ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hx₀A)
    have hYĀ : primeFormConjHom h (idGram F (m + 1)) Y ∈ (A0.subgroupOf N).map ψ :=
      hY ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hy₀A)
    have hZĀ : primeFormConjHom h (idGram F (m + 1)) Z ∈ (A0.subgroupOf N).map ψ :=
      hZ ▸ Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hz₀A)
    have hcommĀ : ∀ a ∈ (A0.subgroupOf N).map ψ, ∀ b ∈ (A0.subgroupOf N).map ψ, a * b = b * a :=
      fun a ha b hb => congrArg Subtype.val (hĀel.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    obtain ⟨u, hu⟩ := exists_smul_comm_of_conj h hn3 X Y (hcommĀ _ hXĀ _ hYĀ)
    obtain ⟨v, hvZ⟩ := exists_smul_comm_of_conj h hn3 X Z (hcommĀ _ hXĀ _ hZĀ)
    obtain ⟨α, hα, hXp⟩ := exists_pow_eq_smul_of_conj h hn3 X (hĀel.2 _ hXĀ)
    have hup : u ^ p = 1 := pow_eq_one_of_smul_comm_p (by omega) hα hXp hu
    have hvp : v ^ p = 1 := pow_eq_one_of_smul_comm_p (by omega) hα hXp hvZ
    have hu1 : u ≠ 1 := by
      rintro rfl
      apply hXY
      apply Subtype.ext
      apply Units.ext
      simp only [Subgroup.coe_mul, Units.val_mul]
      rw [hu, one_smul]
    have hprim : IsPrimitiveRoot u p := by
      rw [← orderOf_eq_prime hup hu1]
      exact IsPrimitiveRoot.orderOf u
    haveI : NeZero p := ⟨hp.ne_zero⟩
    obtain ⟨t, htp, hut⟩ := hprim.eq_pow_of_pow_eq_one hvp
    set i := p - t with hi
    set W : primeFormUnitary h (idGram F (m + 1)) := Y ^ i * Z with hW
    have hWX : W * X = X * W := by
      apply Subtype.ext
      apply Units.ext
      simp only [hW, Subgroup.coe_mul, SubgroupClass.coe_pow, Units.val_mul, Units.val_pow_eq_pow_val]
      set Xm := ((X : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      set Ym := ((Y : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      set Zm := ((Z : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      have hYi := qcommMat_pow_left hu i
      have hvu : v * u ^ i = 1 := by
        rw [← hut, ← pow_add, show t + i = p by omega, hup]
      calc Ym ^ i * Zm * Xm = Ym ^ i * (Zm * Xm) := Matrix.mul_assoc _ _ _
        _ = Ym ^ i * (v • (Xm * Zm)) := by rw [hvZ]
        _ = v • ((Ym ^ i * Xm) * Zm) := by rw [Matrix.mul_smul, Matrix.mul_assoc]
        _ = v • ((u ^ i • (Xm * Ym ^ i)) * Zm) := by rw [hYi]
        _ = (v * u ^ i) • (Xm * (Ym ^ i * Zm)) := by
          rw [Matrix.smul_mul, smul_smul, Matrix.mul_assoc]
        _ = Xm * (Ym ^ i * Zm) := by rw [hvu, one_smul]
    set w : G := y₀ ^ i * z₀ with hw
    have hwA : w ∈ A0 := A0.mul_mem (A0.pow_mem hy₀A i) hz₀A
    set w' : ↥N := ⟨w, hN hwA⟩ with hw'
    have hwW : primeFormConjHom h (idGram F (m + 1)) W = ψ w' := by
      have hw'e : w' = y' ^ i * z' := Subtype.ext rfl
      rw [hw'e, map_mul ψ, map_pow ψ, ← hY, ← hZ, hW, map_mul, map_pow]
    have hwx : (w' : G) ∉ Subgroup.zpowers (x' : G) := by
      intro hmem
      apply hz₀D
      have hz : z₀ = (y₀ ^ i)⁻¹ * w := by rw [hw]; group
      rw [hz]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.pow_mem _
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers _)) _)) (Subgroup.mem_sup_left hmem)
    exact hcommPlane x' hx₀A hx₀1 w' hwA hwx X W hX hwW hWX.symm

end Thm4

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs256g

end
