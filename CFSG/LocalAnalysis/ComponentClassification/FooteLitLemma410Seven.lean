module

public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410Frattini
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFoote47Central
public import CFSG.LocalAnalysis.ComponentClassification.FooteLitLemma410Layer

public section

namespace CFSG.ComponentClassification.FooteLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
  CFSG.ComponentClassification.UnbalancedCorr CFSG.ABGLocalTools GSThmB
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem zpow_eq_one_or_eq_of_mul_self {e : G} (he : e * e = 1) (n : ℤ) : e ^ n = 1 ∨ e ^ n = e := by
  have h2 : e ^ (2 : ℤ) = 1 := by rw [zpow_two, he]
  rcases Int.even_or_odd n with ⟨k, rfl⟩ | ⟨k, rfl⟩
  · left
    rw [← two_mul, zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

omit [Finite G] in
theorem mul_self_mem_of_mem_zpowers_sup {D : Subgroup G} {e : G} (he : e * e = 1)
    (heD : e ∈ normalizer (D : Set G)) {w : G} (hw : w ∈ zpowers e ⊔ D) : w * w ∈ D := by
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right (zpowers e) D
    (zpowers_le.mpr heD)] at hw
  obtain ⟨z, hz, d, hd, rfl⟩ := Set.mem_mul.mp hw
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
  have heinv : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  rcases zpow_eq_one_or_eq_of_mul_self he n with h1 | h1 <;> rw [h1]
  · rw [one_mul]
    exact mul_mem hd hd
  · have h2 : e * d * e⁻¹ ∈ D := (mem_normalizer_iff.mp heD d).mp hd
    rw [heinv] at h2
    rw [show e * d * (e * d) = e * d * e * d by group]
    exact mul_mem h2 hd

omit [Finite G] in
theorem false_of_card_eight_of_dihedral [Finite G]
    (hD : ∀ P : Sylow 2 G, Nonempty ((P : Subgroup G) ≃* DihedralGroup 4))
    {A : Subgroup G} (hA2 : ∀ x ∈ A, x ^ 2 = 1) (hA8 : Nat.card A = 8) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp : IsPGroup 2 A := IsPGroup.of_card (n := 3) (by rw [hA8]; norm_num)
  obtain ⟨P, hAP⟩ := hAp.exists_le_sylow
  obtain ⟨eD⟩ := hD P
  have hP8 : Nat.card (P : Subgroup G) = 8 := by
    rw [Nat.card_congr eD.toEquiv, DihedralGroup.nat_card]
  have hAPeq : A = P := eq_of_le_of_card_ge hAP (by rw [hA8, hP8])
  have hnc : ∃ a b : DihedralGroup 4, a * b ≠ b * a :=
    ⟨DihedralGroup.r 1, DihedralGroup.sr 0, by decide⟩
  obtain ⟨a, b, hab⟩ := hnc
  apply hab
  have h1 : ((eD.symm a : ↥(P : Subgroup G)) : G) * (eD.symm b : ↥(P : Subgroup G)) =
      (eD.symm b : ↥(P : Subgroup G)) * (eD.symm a : ↥(P : Subgroup G)) :=
    commute_of_sq_eq_one hA2 (hAPeq ▸ (eD.symm a).2) (hAPeq ▸ (eD.symm b).2)
  apply eD.symm.injective
  rw [map_mul, map_mul]
  exact Subtype.ext h1

theorem card_le_sixteen_of_isPGroup_perm {T : Subgroup (Equiv.Perm (Fin 7))}
    (hT : IsPGroup 2 T) : Nat.card T ≤ 16 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hT
  have hcard : Nat.card (Equiv.Perm (Fin 7)) = 5040 := by
    rw [Nat.card_perm, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hdvd : 2 ^ k ∣ 5040 := by
    rw [← hk, ← hcard]
    exact T.card_subgroup_dvd_card
  have hk4 : k ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ∣ 5040 := (Nat.pow_dvd_pow 2 (by omega)).trans hdvd
    norm_num at this
  rw [hk]
  calc 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) hk4
    _ = 16 := by norm_num

theorem Foote410Config.exists_mem_not_mem_sup
    (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) {g : G} {E Q : Subgroup G} {t : G}
    (hc : Foote410Config M g E Q t)
    (hseven : Nonempty (L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin 7))) :
    ∃ e₀ ∈ E, e₀ ∉ M ⊔ coreActionKernel M := by
  classical
  obtain ⟨e⟩ := hseven
  obtain ⟨hs, ⟨ε⟩⟩ := hM.quotient h
  by_contra hall
  push Not at hall
  set N := normalizer (M : Set G) with hN
  set Φ := footeAct ε with hΦ
  have : IsSimpleGroup (M ⧸ pPrimeCore 2 M) := hs
  have hZM := (open_isQuasisimple_of_isSimpleGroup (hM.exists_mul_ne h)).2
  have hZ : center (L ⧸ Open.fusionZStar L) = ⊥ :=
    GorensteinWalter.center_eq_bot_of_mulEquiv ε.symm hZM
  have hcinj := injective_mulAut_conj hZ
  set Ē := (E.subgroupOf N).map Φ with hĒ
  have hĒI : Ē ≤ (MulAut.conj : (L ⧸ Open.fusionZStar L) →* _).range := by
    rintro _ ⟨x, hx, rfl⟩
    exact footeAct_mem_range_of_mem_sup ε (hall _ hx)
  set A := Ē.comap (MulAut.conj : (L ⧸ Open.fusionZStar L) →* _) with hA
  have hAmap : A.map (MulAut.conj : (L ⧸ Open.fusionZStar L) →* _) = Ē := map_comap_eq_self hĒI
  have hEN : E ≤ N := hc.hEN
  have hinj : Function.Injective (Φ.comp (E.subgroupOf N).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    apply Subtype.ext
    apply Subtype.ext
    have hxC := mem_coreActionKernel_of_footeAct_eq_one ε hx
    exact hc.eq_one (IsPGroup.of_card (n := 3) (by rw [hc.hE8]; norm_num)) x.2 hxC (hc.hEC x.2)
  have hA8 : Nat.card A = 8 := by
    rw [← card_map_of_injective hcinj, hAmap, ← hc.hE8]
    have hr : (Φ.comp (E.subgroupOf N).subtype).range = Ē := by
      rw [MonoidHom.range_comp, range_subtype]
    rw [← hr, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    exact Nat.card_congr (subgroupOfEquivOfLe hEN).toEquiv
  have hA2 : ∀ x ∈ A, x ^ 2 = 1 := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := (show MulAut.conj x ∈ Ē from hx)
    apply hcinj
    rw [map_pow, ← hyx, ← map_pow, map_one]
    have hy2 : y ^ 2 = 1 := Subtype.ext (by simpa using hc.hE2 (y : G) hy)
    rw [hy2, map_one]
  exact false_of_card_eight_of_dihedral (AutL2Facts.sylow_two_dihedral_a7 e) hA2 hA8

theorem card_le_of_isPGroup_le_normalizer_of_seven
    (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M)
    (hseven : Nonempty (L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin 7)))
    (hC8 : ∀ X : Subgroup G, IsPGroup 2 X → X ≤ coreActionKernel M → Nat.card X ≤ 8)
    {X : Subgroup G} (hX : IsPGroup 2 X) (hXN : X ≤ normalizer (M : Set G)) :
    Nat.card X ≤ 128 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e⟩ := hseven
  obtain ⟨-, ⟨ε⟩⟩ := hM.quotient h
  set N := normalizer (M : Set G) with hN
  set Ψ : MulAut (L ⧸ Open.fusionZStar L) ≃* Equiv.Perm (Fin 7) :=
    (MulAut.congr e).trans AutL2Facts.a7AutEquiv.symm with hΨ
  set f := (Ψ.toMonoidHom.comp (footeAct ε)).comp (X.subgroupOf N).subtype with hf
  have hc1 : Nat.card ↥(X.subgroupOf N) = Nat.card f.range * Nat.card f.ker := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
    exact Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hr : Nat.card f.range ≤ 16 := by
    apply card_le_sixteen_of_isPGroup_perm
    have hXs : IsPGroup 2 ↥(X.subgroupOf N) := hX.comap_subtype
    rw [MonoidHom.range_eq_map]
    exact (hXs.to_subgroup ⊤).map f
  have hk : Nat.card f.ker ≤ 8 := by
    set ι := N.subtype.comp (X.subgroupOf N).subtype with hι
    have hιinj : Function.Injective ι := N.subtype_injective.comp (X.subgroupOf N).subtype_injective
    rw [← card_map_of_injective hιinj]
    have hle : f.ker.map ι ≤ X ⊓ coreActionKernel M := by
      rintro _ ⟨k, hk, rfl⟩
      refine mem_inf.mpr ⟨(k : ↥(X.subgroupOf N)).2, ?_⟩
      have h1 : Ψ (footeAct ε ((X.subgroupOf N).subtype k)) = 1 := hk
      rw [map_eq_one_iff _ Ψ.injective] at h1
      exact mem_coreActionKernel_of_footeAct_eq_one ε h1
    exact (card_le_of_le hle).trans (hC8 _ (hX.to_le inf_le_left) inf_le_right)
  rw [← Nat.card_congr (subgroupOfEquivOfLe hXN).toEquiv, hc1]
  calc Nat.card f.range * Nat.card f.ker ≤ 16 * 8 := Nat.mul_le_mul hr hk
    _ = 128 := by norm_num

omit [Finite G] in
theorem mem_normalizer_of_forall_mul_comm {H : Subgroup G} {x : G}
    (hx : ∀ h ∈ H, x * h = h * x) : x ∈ normalizer (H : Set G) := by
  rw [mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [hx y hy, mul_inv_cancel_right]
    exact hy
  · intro hy
    have h2 : x * (x * y * x⁻¹) = x * y := by rw [hx _ hy]; group
    have h3 : x * y * x⁻¹ = y := mul_left_cancel h2
    rwa [h3] at hy

theorem Foote410Config.exists_isSylowOf_sq_mem
    (h : FooteSec4 G L) {M : Subgroup G} (hM : IsFooteM L M) {g : G} {E Q : Subgroup G} {t : G}
    (hc : Foote410Config M g E Q t)
    (hseven : Nonempty (L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin 7)))
    (hC8 : ∀ X : Subgroup G, IsPGroup 2 X → X ≤ coreActionKernel M → Nat.card X ≤ 8) :
    ∃ S D₀ : Subgroup G, IsSylowOf 2 S (normalizer (M : Set G)) ∧ (∀ s ∈ S, s * s ∈ D₀) ∧
      D₀ ⊓ coreActionKernel M = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := coreActionKernel M with hC
  set N := normalizer (M : Set G) with hN
  obtain ⟨e₀, he₀E, he₀MC⟩ := hc.exists_mem_not_mem_sup h hM hseven
  have he₀2 : e₀ * e₀ = 1 := by rw [← sq]; exact hc.hE2 e₀ he₀E
  have he₀N : e₀ ∈ N := hc.hEN he₀E
  have hQp : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by rw [hc.hQ8]; norm_num)
  have hQN : Q ≤ N := hc.hQC.trans fun c hc' => (mem_coreActionKernel.mp hc').1
  have he₀Q : ∀ q ∈ Q, e₀ * q = q * e₀ := fun q hq => hc.hEQ e₀ he₀E q hq
  have hzQ : zpowers e₀ ≤ normalizer (Q : Set G) :=
    zpowers_le.mpr (mem_normalizer_of_forall_mul_comm he₀Q)
  have hQep : IsPGroup 2 ↥(Q ⊔ zpowers e₀) := hQp.to_sup_of_normal_left'
    (isPGroup_two_zpowers_of_sq_eq_one (by rw [sq]; exact he₀2)) hzQ
  obtain ⟨D₀, hD₀, -, hD₀N⟩ := exists_isSylowOf_ge_le_normalizer
    (sup_le hQN (zpowers_le.mpr he₀N)) (bot_le : ⊥ ≤ M) (by rw [sup_bot_eq]; exact hQep)
  have hD₀M : D₀ ≤ M := hD₀.le
  have hD₀p : IsPGroup 2 D₀ := hD₀.isPGroup
  have hD₀C : D₀ ⊓ C = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    exact (mem_bot).mpr (eq_one_of_mem_of_odd hD₀p (odd_card_oddCoreIn M) (mem_inf.mp hx).1
      (hM.inf_coreActionKernel_le h (mem_inf.mpr ⟨hD₀M (mem_inf.mp hx).1, (mem_inf.mp hx).2⟩)))
  have hQD : ∀ q ∈ Q, ∀ d ∈ D₀, q * d = d * q := by
    intro q hq d hd
    have hc1 : q * d * q⁻¹ * d⁻¹ ∈ D₀ :=
      mul_mem ((mem_normalizer_iff.mp (hD₀N (mem_sup_left hq)) d).mp hd) (inv_mem hd)
    have hc2 : q * d * q⁻¹ * d⁻¹ ∈ C := by
      have : d * q⁻¹ * d⁻¹ ∈ C :=
        (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M
          (le_normalizer (hD₀M hd))) _).mp (inv_mem (hc.hQC hq))
      rw [show q * d * q⁻¹ * d⁻¹ = q * (d * q⁻¹ * d⁻¹) by group]
      exact mul_mem (hc.hQC hq) this
    have hc3 : q * d * q⁻¹ * d⁻¹ = 1 := by
      have := mem_inf.mpr ⟨hc1, hc2⟩
      rw [hD₀C] at this
      exact (mem_bot).mp this
    calc q * d = q * d * q⁻¹ * d⁻¹ * (d * q) := by group
      _ = d * q := by rw [hc3, one_mul]
  have he₀D : e₀ ∈ normalizer (D₀ : Set G) := hD₀N (mem_sup_right (mem_zpowers e₀))
  set X₀ := zpowers e₀ ⊔ D₀ with hX₀
  have hQX₀ : ∀ q ∈ Q, ∀ w ∈ X₀, q * w = w * q := by
    intro q hq w hw
    have hle : X₀ ≤ centralizer ({q} : Set G) := sup_le
      (zpowers_le.mpr (mem_centralizer_singleton_iff.mpr (he₀Q q hq)))
      (fun d hd => mem_centralizer_singleton_iff.mpr (hQD q hq d hd).symm)
    exact (mem_centralizer_singleton_iff.mp (hle hw)).symm
  have hQX₀N : Q ≤ normalizer (X₀ : Set G) := fun q hq =>
    mem_normalizer_of_forall_mul_comm (hQX₀ q hq)
  set S := Q ⊔ X₀ with hS
  have hSsq : ∀ s ∈ S, s * s ∈ D₀ := by
    intro s hs
    rw [← SetLike.mem_coe, hS, coe_mul_of_left_le_normalizer_right Q X₀ hQX₀N] at hs
    obtain ⟨q, hq, w, hw, rfl⟩ := Set.mem_mul.mp hs
    have hq2 : q * q = 1 := by rw [← sq]; exact hc.hQ2 q hq
    have h1 : q * w * (q * w) = q * q * (w * w) := by
      calc q * w * (q * w) = q * (w * q) * w := by group
        _ = q * (q * w) * w := by rw [← hQX₀ q hq w hw]
        _ = q * q * (w * w) := by group
    rw [h1, hq2, one_mul]
    exact mul_self_mem_of_mem_zpowers_sup he₀2 he₀D hw
  obtain ⟨e⟩ := hseven
  obtain ⟨-, ⟨ε⟩⟩ := hM.quotient h
  have hMbar : Nat.card (M ⧸ pPrimeCore 2 M) = 2520 := by
    rw [Nat.card_congr (ε.trans e).toEquiv]
    exact AutL2Facts.card_alternatingGroup_seven
  have hD₀8 : Nat.card D₀ = 8 := by
    rw [hD₀.card_eq, Subgroup.card_eq_card_quotient_mul_card_subgroup (pPrimeCore 2 ↥M), hMbar]
    have hodd := odd_card_pPrimeCore_two ↥M
    have h0 : Nat.card (pPrimeCore 2 ↥M) ≠ 0 := Nat.card_pos.ne'
    have h2 : ¬ 2 ∣ 315 * Nat.card (pPrimeCore 2 ↥M) := fun h2 =>
      (Nat.not_even_iff_odd.mpr (Odd.mul (by decide : Odd 315) hodd)) (even_iff_two_dvd.mpr h2)
    rw [show 2520 * Nat.card (pPrimeCore 2 ↥M) = 2 ^ 3 * (315 * Nat.card (pPrimeCore 2 ↥M)) by
      ring, Nat.factorization_mul (by norm_num) (by positivity), Nat.factorization_pow]
    simp [Nat.prime_two.factorization_self, Nat.factorization_eq_zero_of_not_dvd h2]
  have he₀1 : e₀ ≠ 1 := fun h1 => he₀MC (h1 ▸ one_mem _)
  have he₀o : orderOf e₀ = 2 := orderOf_eq_prime (by rw [sq]; exact he₀2) he₀1
  have hzD : D₀ ⊓ zpowers e₀ = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp (mem_inf.mp hx).2
    rcases zpow_eq_one_or_eq_of_mul_self he₀2 n with h1 | h1
    · rw [h1]
      exact one_mem _
    · exfalso
      have h2 := (mem_inf.mp hx).1
      rw [h1] at h2
      exact he₀MC (mem_sup_left (hD₀M h2))
  have hX₀card : Nat.card X₀ = 16 := by
    have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer (A := D₀) (B := zpowers e₀)
      (zpowers_le.mpr he₀D)
    rw [hzD, card_bot, mul_one, hD₀8, Nat.card_zpowers, he₀o, sup_comm] at h1
    rw [hX₀, h1]
  have hX₀Q : X₀ ⊓ Q = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hxC : x ∈ C := hc.hQC (mem_inf.mp hx).2
    have hxX := (mem_inf.mp hx).1
    rw [← SetLike.mem_coe, hX₀, coe_mul_of_left_le_normalizer_right (zpowers e₀) D₀
      (zpowers_le.mpr he₀D)] at hxX
    obtain ⟨z, hz, d, hd, rfl⟩ := Set.mem_mul.mp hxX
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hz
    rcases zpow_eq_one_or_eq_of_mul_self he₀2 n with h1 | h1 <;> rw [h1] at hxC ⊢
    · rw [one_mul] at hxC ⊢
      have := mem_inf.mpr ⟨hd, hxC⟩
      rwa [hD₀C] at this
    · exfalso
      apply he₀MC
      rw [show e₀ = e₀ * d * d⁻¹ by group]
      exact mul_mem (mem_sup_right hxC) (mem_sup_left (inv_mem (hD₀M hd)))
  have hScard : Nat.card S = 128 := by
    have h1 := CFSG.Walter.W67.card_sup_mul_card_inf_of_le_normalizer (A := X₀) (B := Q) hQX₀N
    rw [hX₀Q, card_bot, mul_one, hX₀card, hc.hQ8, sup_comm] at h1
    rw [hS, h1]
  have hSN : S ≤ N := sup_le hQN (sup_le (zpowers_le.mpr he₀N) (hD₀M.trans le_normalizer))
  have hSp : IsPGroup 2 S := IsPGroup.of_card (n := 7) (by rw [hScard]; norm_num)
  obtain ⟨T, hT, hST⟩ := exists_isSylowOf_ge_of_le hSN hSp
  have hT128 := card_le_of_isPGroup_le_normalizer_of_seven h hM ⟨e⟩ hC8 hT.isPGroup hT.le
  have hTS : S = T := eq_of_le_of_card_ge hST (by rw [hScard]; exact hT128)
  exact ⟨S, D₀, hTS ▸ hT, hSsq, hD₀C⟩

theorem Foote410Config.false_of_seven
    (h : FooteSec4 G L) (h47 : FooteThm47Statement) (hST : GSThmB.SuzukiTausskyInput)
    (hAsc : Foote5.AschbacherCentralCoreInput) (h2An : GSThmB.Solomon2AnInput) {M : Subgroup G}
    (hM : IsFooteM L M) {g : G} {E Q : Subgroup G} {t : G} (hc : Foote410Config M g E Q t)
    (htK : t ∉ footeK L t)
    (hseven : Nonempty (L ⧸ Open.fusionZStar L ≃* alternatingGroup (Fin 7))) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, x, hxE, hx1, hxK⟩ :=
    hc.exists_mem_coreActionKernel_footeK h h47 hST hAsc h2An hM htK
  obtain ⟨hK₀M', hVK₀, -⟩ :=
    hc.le_conjugate_of_mem_coreActionKernel h h47 hST hAsc h2An hM htK hxE hx1 hxK
  set K := footeK L t with hK
  set V := Q ⊓ K with hVdef
  set M' := conjugate M g with hM'def
  have hV4 := hc.card_inf_footeK h h47 hST hAsc h2An hM htK
  have hV : IsKleinFour V := isKleinFour_of_card_eq_four hV4 fun v hv =>
    hc.hQ2 v (mem_inf.mp hv).1
  have hVM' : V ≤ M' := hVK₀.trans hK₀M'
  have hVC : V ≤ coreActionKernel M := inf_le_left.trans hc.hQC
  have hC8 : ∀ X : Subgroup G, IsPGroup 2 X → X ≤ coreActionKernel M → Nat.card X ≤ 8 :=
    fun X hX hXC => hc.card_le_eight_of_le h h47 hST hM hV hVM' hVC hX hXC
  obtain ⟨e⟩ := hseven
  obtain ⟨-, ⟨ε'⟩⟩ := (isFooteM_conjugate h hM g).quotient h
  obtain ⟨y, hyV, hy1, s, ⟨k, hk⟩, hsy⟩ :=
    exists_sq_eq_of_isKleinFour (AutL2Facts.sylow_two_dihedral_a7 (ε'.trans e)) hV hVM'
  have hy2 : orderOf y = 2 := orderOf_eq_prime (hc.hQ2 y (mem_inf.mp hyV).1) hy1
  have hyC : y ∈ coreActionKernel M := hVC hyV
  obtain ⟨Sy, hSy, hSyN⟩ := exists_isSylowOf_centralizer_le_normalizer h h47 hST hM hy2 hyC
  have hsy' : s ∈ centralizer ({y} : Set G) := mem_centralizer_singleton_iff.mpr (by
    rw [← hsy, sq, mul_assoc])
  have hsp : IsPGroup 2 (zpowers s) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨c, hcy, hcs⟩ := exists_conj_le_of_isSylowOf hSy (zpowers_le.mpr hsy') hsp
  have hs'S : c⁻¹ * s * c ∈ Sy := hcs s (mem_zpowers s)
  have hcy' : c * y = y * c := mem_centralizer_singleton_iff.mp hcy
  have hs'y : c⁻¹ * s * c * (c⁻¹ * s * c) = y := by
    calc c⁻¹ * s * c * (c⁻¹ * s * c) = c⁻¹ * s ^ 2 * c := by rw [sq]; group
      _ = c⁻¹ * (c * y) := by rw [hsy, mul_assoc, hcy']
      _ = y := by group
  obtain ⟨S, D₀, hS, hSsq, hD₀C⟩ := hc.exists_isSylowOf_sq_mem h hM ⟨e⟩ hC8
  have hs'N : c⁻¹ * s * c ∈ normalizer (M : Set G) := hSyN hs'S
  have hs'p : IsPGroup 2 (zpowers (c⁻¹ * s * c)) :=
    hSy.isPGroup.to_le (zpowers_le.mpr hs'S)
  obtain ⟨n, hnN, hn⟩ := exists_conj_le_of_isSylowOf hS (zpowers_le.mpr hs'N) hs'p
  have h1 := hSsq _ (hn _ (mem_zpowers (c⁻¹ * s * c)))
  have h2 : n⁻¹ * (c⁻¹ * s * c) * n * (n⁻¹ * (c⁻¹ * s * c) * n) = n⁻¹ * y * n := by
    rw [← hs'y]
    group
  rw [h2] at h1
  have h3 : n⁻¹ * y * n ∈ coreActionKernel M := by
    have := (mem_normalizer_iff.mp (normalizer_le_normalizer_coreActionKernel M
      (inv_mem hnN)) y).mp hyC
    rwa [inv_inv] at this
  have h4 := mem_inf.mpr ⟨h1, h3⟩
  rw [hD₀C, mem_bot] at h4
  apply hy1
  calc y = n * (n⁻¹ * y * n) * n⁻¹ := by group
    _ = 1 := by rw [h4]; group

end CFSG.ComponentClassification.FooteLit
