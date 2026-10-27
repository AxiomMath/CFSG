module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5SwapA

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS CFSG.LocalCores
  CFSG.ComponentClassification.Sol76 CFSG.ComponentClassification.CatalogueBPrimeJoin

open scoped commutatorElement

structure SwapDiag (X : Type) [Group X] [Finite X] (n : ℕ) (z s : X) (M Δ : Subgroup X) :
    Prop where
  comp : Sec5Comp X n (centralizer ({z} : Set X)) M
  comm : z * s = s * z
  moved : M.map (MulAut.conj s).toMonoidHom ≠ M
  le_cen : Δ ≤ centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X)
  isPComp : IsPCompIn 2 (centralizer ({z} : Set X) ⊓ centralizer ({s} : Set X)) Δ
  perfect : ⁅Δ, Δ⁆ = Δ
  twoGen : primeResidual 2 ↥Δ = ⊤
  quot : Nonempty (↥Δ ⧸ pPrimeCore 2 ↥Δ ≃* alternatingGroup (Fin n))
  covers_diag : ∀ m ∈ M, m * (s * m * s⁻¹) ∈ Δ ⊔ oddCoreOf (centralizer ({z} : Set X))
  cen_fixed : ∀ c ∈ M, (∀ m ∈ M, ⁅m, c⁆ ∈ oddCoreOf M) →
    s * c * s⁻¹ * c⁻¹ ∈ oddCoreOf (centralizer ({z} : Set X))

section Aux

variable {X : Type} [Group X]

private theorem mem_oddCoreOf_iff_subtype {C : Subgroup X} (x : ↥C) :
    (x : X) ∈ oddCoreOf C ↔ x ∈ pPrimeCore 2 ↥C :=
  ⟨fun h => (mem_oddCoreOf_iff.1 h).2, fun h => mem_oddCoreOf_iff.2 ⟨x.2, h⟩⟩

end Aux

section Core

variable {C : Type} [Group C] [Finite C]

private theorem mul_self_eq_one_of_mem_center_of_card_two {K : Type} [Group K]
    (hc : Nat.card (center K) = 2) {v : K} (hv : v ∈ center K) : v * v = 1 := by
  have h1 : orderOf (⟨v, hv⟩ : center K) ∣ Nat.card (center K) := orderOf_dvd_natCard _
  rw [hc] at h1
  have h2 : (⟨v, hv⟩ : center K) ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 h1
  simpa [pow_two] using congrArg Subtype.val h2

private theorem diagLift_core {B : Subgroup C} (hB : IsPComponent 2 B) {t : C} (ht : t * t = 1)
    (hne : B.map (MulAut.conj t).toMonoidHom ≠ B) :
    ∃ Δ : Subgroup C, Δ ≤ centralizer ({t} : Set C) ∧
      IsPComponent 2 (Δ.subgroupOf (centralizer ({t} : Set C))) ∧
      (∀ b ∈ B, b * (t * b * t⁻¹) ∈ Δ ⊔ pPrimeCore 2 C) ∧
      (∀ d ∈ Δ, ∃ b ∈ B, d * (b * (t * b * t⁻¹))⁻¹ ∈ pPrimeCore 2 C) ∧
      ∀ {n : ℕ}, IsDoubleCoverOfAlt (↥B ⧸ pPrimeCore 2 ↥B) n →
        (∀ c ∈ B, (∀ b ∈ B, ⁅b, c⁆ ∈ pPrimeCore 2 C) → t * c * t⁻¹ * c⁻¹ ∈ pPrimeCore 2 C) →
        Nonempty (↥Δ ⧸ pPrimeCore 2 ↥Δ ≃* alternatingGroup (Fin n)) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π : C →* C ⧸ pPrimeCore 2 C := QuotientGroup.mk' (pPrimeCore 2 C) with hπ
  set B' : Subgroup C := B.map (MulAut.conj t).toMonoidHom with hB'
  have hB'pc : IsPComponent 2 B' :=
    LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (MulAut.conj t) hB
  have hKc : IsComponent (B.map π) := by
    obtain ⟨K, hK, -, hKeq, -⟩ := hB
    exact hKeq ▸ hK
  set g : C ⧸ pPrimeCore 2 C := π t with hg
  have hg2 : g * g = 1 := by rw [hg, ← map_mul, ht, map_one]
  have hKK' : (B.map π).map (MulAut.conj g).toMonoidHom = B'.map π := by
    rw [Subgroup.map_map, hB', Subgroup.map_map]
    congr 1
  have hne' : (B.map π).map (MulAut.conj g).toMonoidHom ≠ B.map π := by
    rw [hKK']
    intro h
    exact hne (eq_of_map_pPrimeCore_eq hB'pc hB h)
  obtain ⟨D, δ, hDq, hDC, hDs, -, hδsur, hδv⟩ := diag_isComponent hKc hg2 hne'
  have hDmem : ∀ v ∈ B.map π, v * (g * v * g⁻¹) ∈ D := fun v hv => by
    have h1 := (δ ⟨v, hv⟩).2
    rw [hδv ⟨v, hv⟩] at h1
    exact h1
  obtain ⟨Δ, hΔC, hΔpc, hΔmap, hΔn⟩ := exists_isPComponent_lift ht hDq hDC hDs
  have hker : ∀ x : C, π x = 1 ↔ x ∈ pPrimeCore 2 C := fun x => QuotientGroup.eq_one_iff x
  refine ⟨Δ, hΔC, hΔpc, ?_, ?_, ?_⟩
  · intro b hb
    have hbD : π (b * (t * b * t⁻¹)) ∈ D := by
      have := hDmem (π b) (Subgroup.mem_map_of_mem π hb)
      simpa [map_mul, map_inv, hg] using this
    rw [← hΔmap] at hbD
    obtain ⟨d, hd, hdb⟩ := Subgroup.mem_map.1 hbD
    have h1 : d⁻¹ * (b * (t * b * t⁻¹)) ∈ pPrimeCore 2 C := by
      rw [← hker, map_mul, map_inv, hdb]
      group
    have : b * (t * b * t⁻¹) = d * (d⁻¹ * (b * (t * b * t⁻¹))) := by group
    rw [this]
    exact Subgroup.mul_mem_sup hd h1
  · intro d hd
    have hdD : π d ∈ D := hΔmap ▸ Subgroup.mem_map_of_mem π hd
    obtain ⟨v, hv⟩ := hδsur ⟨π d, hdD⟩
    obtain ⟨b, hb, hbv⟩ := Subgroup.mem_map.1 v.2
    refine ⟨b, hb, ?_⟩
    have h1 : (π d : C ⧸ pPrimeCore 2 C) = (v : C ⧸ pPrimeCore 2 C) * (g * v * g⁻¹) := by
      have := hδv v
      rw [hv] at this
      exact this
    have h2 : π d = π (b * (t * b * t⁻¹)) := by
      rw [h1, ← hbv]
      simp [map_mul, map_inv, hg]
    rw [← hker, map_mul, map_inv, h2, mul_inv_cancel]
  · intro n hcov hcen
    obtain ⟨e₁⟩ := exists_mulEquiv_quot_image hB
    have hK'c : IsComponent ((B.map π).map (MulAut.conj g).toMonoidHom) :=
      isComponent_map_mulEquiv (MulAut.conj g) hKc
    have hZc : Nat.card (center ↥(B.map π)) = 2 := by
      rw [← Nat.card_congr (Subgroup.centerCongr e₁).toEquiv]
      exact hcov.2.1
    have hZK : IsPGroup 2 ↥(center ↥(B.map π)) :=
      IsPGroup.of_card (n := 1) (by rw [hZc, pow_one])
    have hZD : IsPGroup 2 ↥(center ↥D) := isPGroup_center_of_surjective hKc.1 hDq hZK δ hδsur
    have hkerδ : δ.ker = center ↥(B.map π) := by
      ext v
      rw [MonoidHom.mem_ker, Subgroup.mem_center_iff]
      constructor
      · intro hv k
        have h1 : ((δ v : ↥D) : C ⧸ pPrimeCore 2 C) = 1 := by rw [hv]; rfl
        rw [hδv] at h1
        have hvK' : (v : C ⧸ pPrimeCore 2 C) ∈ (B.map π).map (MulAut.conj g).toMonoidHom := by
          have e : (v : C ⧸ pPrimeCore 2 C) = (g * v * g⁻¹)⁻¹ := eq_inv_of_mul_eq_one_left h1
          rw [e]
          exact inv_mem (conj_mem_map_conj v.2)
        exact Subtype.ext (commute_of_ne hKc hK'c (fun h => hne' h.symm) k.2 hvK').eq
      · intro hv
        obtain ⟨c, hc, hcv⟩ := Subgroup.mem_map.1 v.2
        have hcomm : ∀ b ∈ B, ⁅b, c⁆ ∈ pPrimeCore 2 C := by
          intro b hb
          rw [← hker, map_commutatorElement]
          have h2 := congrArg Subtype.val (hv ⟨π b, Subgroup.mem_map_of_mem π hb⟩)
          refine commutatorElement_eq_one_iff_mul_comm.2 ?_
          rw [hcv]
          exact h2
        have h3 := (hker _).2 (hcen c hc hcomm)
        have h4 : g * (v : C ⧸ pPrimeCore 2 C) * g⁻¹ = v := by
          rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcv] at h3
          have h5 : g * (v : C ⧸ pPrimeCore 2 C) * g⁻¹ * (v : C ⧸ pPrimeCore 2 C)⁻¹ = 1 := by
            simpa [hg] using h3
          exact mul_inv_eq_one.1 h5
        have hv2 : v * v = 1 := mul_self_eq_one_of_mem_center_of_card_two hZc
          (Subgroup.mem_center_iff.2 hv)
        apply Subtype.ext
        rw [hδv, h4]
        have := congrArg Subtype.val hv2
        simpa using this
    let ψ : ↥Δ →* ↥D := (π.comp Δ.subtype).codRestrict D (fun x => by
      rw [← hΔmap]
      exact Subgroup.mem_map_of_mem π x.2)
    have hψ : Function.Surjective ψ := by
      rintro ⟨d, hd⟩
      obtain ⟨x, hx, hxd⟩ := Subgroup.mem_map.1 (hΔmap ▸ hd)
      exact ⟨⟨x, hx⟩, Subtype.ext hxd⟩
    have hψker : ψ.ker = pPrimeCore 2 ↥Δ := by
      apply le_antisymm
      · have hle : ψ.ker.map Δ.subtype ≤ pPrimeCore 2 C := by
          rintro _ ⟨x, hx, rfl⟩
          have h1 : ψ x = 1 := hx
          have h2 : π (x : C) = 1 := by
            have := congrArg Subtype.val h1
            exact this
          exact (hker _).1 h2
        have hdvd : Nat.card ψ.ker ∣ Nat.card (pPrimeCore 2 C) := by
          rw [← Subgroup.card_map_of_injective (K := ψ.ker) Δ.subtype_injective]
          exact Subgroup.card_dvd_of_le hle
        exact le_sSup ⟨inferInstance, Nat.Coprime.of_dvd_right hdvd pPrimeCore_coprime_card⟩
      · intro x hx
        have hRn : (Subgroup.map ψ (pPrimeCore 2 ↥Δ)).Normal :=
          Subgroup.Normal.map pPrimeCore_normal ψ hψ
        have hodd : Odd (Nat.card (Subgroup.map ψ (pPrimeCore 2 ↥Δ))) :=
          Nat.coprime_two_left.1 (Nat.Coprime.of_dvd_right (Subgroup.card_map_dvd _ ψ)
            pPrimeCore_coprime_card)
        have hbot := normal_odd_eq_bot_of_quasisimple hDq hZD hodd
        have : ψ x ∈ Subgroup.map ψ (pPrimeCore 2 ↥Δ) := Subgroup.mem_map_of_mem ψ hx
        rw [hbot, Subgroup.mem_bot] at this
        exact this
    let e₅ : ↥Δ ⧸ pPrimeCore 2 ↥Δ ≃* ↥D :=
      (QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
    let e₂ : ↥(B.map π) ⧸ center ↥(B.map π) ≃* ↥D :=
      (QuotientGroup.quotientMulEquivOfEq hkerδ.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective δ hδsur)
    let e₃ : (↥B ⧸ pPrimeCore 2 ↥B) ⧸ center (↥B ⧸ pPrimeCore 2 ↥B) ≃*
        ↥(B.map π) ⧸ center ↥(B.map π) :=
      QuotientGroup.congr _ _ e₁ (Subgroup.map_center_eq e₁)
    obtain ⟨e₄⟩ := hcov.2.2
    exact ⟨e₅.trans (e₂.symm.trans (e₃.symm.trans e₄))⟩

end Core

section DiagLift

variable {X : Type} [Group X] [Finite X]

theorem exists_diagLift {C M : Subgroup X} (hM : IsPCompIn 2 C M) {t : X} (htC : t ∈ C)
    (ht : t * t = 1) (hne : M.map (MulAut.conj t).toMonoidHom ≠ M) :
    ∃ Δ : Subgroup X, Δ ≤ C ⊓ centralizer ({t} : Set X) ∧
      IsPCompIn 2 (C ⊓ centralizer ({t} : Set X)) Δ ∧
      (∀ m ∈ M, m * (t * m * t⁻¹) ∈ Δ ⊔ oddCoreOf C) ∧
      (∀ d ∈ Δ, ∃ m ∈ M, d * (m * (t * m * t⁻¹))⁻¹ ∈ oddCoreOf C) ∧
      ∀ {n : ℕ}, IsDoubleCoverOfAlt (↥M ⧸ pPrimeCore 2 ↥M) n →
        (∀ c ∈ M, (∀ m ∈ M, ⁅m, c⁆ ∈ oddCoreOf M) → t * c * t⁻¹ * c⁻¹ ∈ oddCoreOf C) →
        Nonempty (↥Δ ⧸ pPrimeCore 2 ↥Δ ≃* alternatingGroup (Fin n)) := by
  classical
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMC : M ≤ C := hM.1
  have hMtC : M.map (MulAut.conj t).toMonoidHom ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact C.mul_mem (C.mul_mem htC (hMC hx)) (C.inv_mem htC)
  set tc : ↥C := ⟨t, htC⟩ with htcdef
  have htc2 : tc * tc = 1 := Subtype.ext ht
  have hBne : (M.subgroupOf C).map (MulAut.conj tc).toMonoidHom ≠ M.subgroupOf C := by
    rw [map_conj_subgroupOf htC M]
    intro heq
    apply hne
    have h1 := heq
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hMtC, inf_of_le_left hMC] at h1
    exact h1
  obtain ⟨Δ₀, hΔ₀C, hΔ₀pc, hc2, hc3, hq⟩ := diagLift_core hM.2 htc2 hBne
  have hΔC : Δ₀.map C.subtype ≤ C := Subgroup.map_subtype_le Δ₀
  have hΔt : Δ₀.map C.subtype ≤ centralizer ({t} : Set X) := by
    rintro _ ⟨x, hx, rfl⟩
    have := Subgroup.mem_centralizer_singleton_iff.1 (hΔ₀C hx)
    exact Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val this)
  have hcenmap : (centralizer ({tc} : Set ↥C)).map C.subtype = C ⊓ centralizer ({t} : Set X) := by
    rw [centralizer_singleton_subgroup htC, Subgroup.subgroupOf_map_subtype, inf_comm]
  have hΔpc : IsPCompIn 2 (C ⊓ centralizer ({t} : Set X)) (Δ₀.map C.subtype) := by
    refine ⟨le_inf hΔC hΔt, ?_⟩
    have h1 := (isPComponent_subgroupOf_map_iff 2 C.subtype C.subtype_injective hΔ₀C).2 hΔ₀pc
    rwa [hcenmap] at h1
  have hoC : ∀ x : ↥C, (x : X) ∈ oddCoreOf C ↔ x ∈ pPrimeCore 2 ↥C := mem_oddCoreOf_iff_subtype
  refine ⟨Δ₀.map C.subtype, le_inf hΔC hΔt, hΔpc, ?_, ?_, ?_⟩
  · intro m hm
    have h1 := hc2 ⟨m, hMC hm⟩ hm
    have h2 := Subgroup.mem_map_of_mem C.subtype h1
    rw [Subgroup.map_sup] at h2
    exact h2
  · rintro _ ⟨d, hd, rfl⟩
    obtain ⟨b, hb, hbd⟩ := hc3 d hd
    exact ⟨(b : X), hb, (hoC _).2 hbd⟩
  · intro n hcov hcen
    have hcov' : IsDoubleCoverOfAlt (↥(M.subgroupOf C) ⧸ pPrimeCore 2 ↥(M.subgroupOf C)) n := by
      obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv (Subgroup.subgroupOfEquivOfLe hMC)
      exact isDoubleCoverOfAlt_congr' f.symm hcov
    have hcen' : ∀ c ∈ M.subgroupOf C, (∀ b ∈ M.subgroupOf C, ⁅b, c⁆ ∈ pPrimeCore 2 ↥C) →
        tc * c * tc⁻¹ * c⁻¹ ∈ pPrimeCore 2 ↥C := by
      intro c hc hcomm
      refine (hoC (tc * c * tc⁻¹ * c⁻¹)).1 (hcen (c : X) hc fun m hm => ?_)
      have h1 := (hoC _).2 (hcomm ⟨m, hMC hm⟩ hm)
      have h2 : ⁅m, (c : X)⁆ ∈ M := by
        simp only [commutatorElement_def]
        exact M.mul_mem (M.mul_mem (M.mul_mem hm hc) (M.inv_mem hm)) (M.inv_mem hc)
      exact inf_oddCoreOf_le hMC ⟨h2, h1⟩
    obtain ⟨e⟩ := hq hcov' hcen'
    obtain ⟨f⟩ := nonempty_quotPPrimeCore_equiv
      (Δ₀.equivMapOfInjective C.subtype C.subtype_injective)
    exact ⟨f.symm.trans e⟩

private theorem commutator_eq_self_of_isPCompIn {H K : Subgroup X} (h : IsPCompIn 2 H K) :
    ⁅K, K⁆ = K := by
  have hp : Group.IsPerfect (K.subgroupOf H) :=
    CFSG.ComponentClassification.CatalogueBAlternating.pComponent_perfect h.2
  have hp' : Group.IsPerfect K := by
    have e := Subgroup.subgroupOfEquivOfLe h.1
    exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
  exact Subgroup.isPerfect_iff.mp hp'

private theorem primeResidual_eq_top_of_isPCompIn {H K : Subgroup X} (h : IsPCompIn 2 H K) :
    primeResidual 2 ↥K = ⊤ :=
  ((isTwoGenQuasi_subgroupOf_iff h.1).1 (isPComponent_two_iff.1 h.2).2).1

variable {n : ℕ} {z : X} {Z : Subgroup X} {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

private theorem cen_fixed_of_comp (h : Sec5Data X n z Z S) (hZs : Z ≤ centralizer ({s} : Set X))
    (hsC : s ∈ centralizer ({z} : Set X)) {M : Subgroup X}
    (hM : Sec5Comp X n (centralizer ({z} : Set X)) M) :
    ∀ c ∈ M, (∀ m ∈ M, ⁅m, c⁆ ∈ oddCoreOf M) →
      s * c * s⁻¹ * c⁻¹ ∈ oddCoreOf (centralizer ({z} : Set X)) := by
  classical
  intro c hcM hc
  obtain ⟨⟨u₀, hu₀⟩, hMn⟩ := id hM
  obtain ⟨u, huZ, hu⟩ := h.pair.exists_witness_mem hu₀ hMn
  have hcz : c ∈ zStar M := ⟨hcM, Subgroup.le_normalizer hcM,
    mem_normalizer_pPrimeCoreOf_of_mem hcM, fun k hk => hc k hk⟩
  have hc' : c ∈ pPrimeCoreOf 2 M ⊔ Subgroup.zpowers u := hu.zStar_le_sup_zpowers hMn hcz
  have hnorm : Subgroup.zpowers u ≤ normalizer (pPrimeCoreOf 2 M : Set X) := by
    rw [Subgroup.zpowers_le]
    exact mem_normalizer_pPrimeCoreOf_of_mem hu.2.1
  obtain ⟨o, ho, w, hw, rfl⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing (pPrimeCoreOf 2 M) (Subgroup.zpowers u)
      hnorm c).1 hc'
  have hwC : w ∈ centralizer ({s} : Set X) :=
    (Subgroup.zpowers_le.2 (hZs huZ)) hw
  have hsw : s * w * s⁻¹ = w := by
    have := Subgroup.mem_centralizer_singleton_iff.1 hwC
    rw [← this]
    group
  have hoO : o ∈ oddCoreOf (centralizer ({z} : Set X)) :=
    oddCoreOf_le_of_isPCompIn hM.isPCompIn ho
  have hso : s * o * s⁻¹ ∈ oddCoreOf (centralizer ({z} : Set X)) :=
    (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf _ hsC) o).1 hoO
  have e : s * (o * w) * s⁻¹ * (o * w)⁻¹ = (s * o * s⁻¹) * o⁻¹ := by
    calc s * (o * w) * s⁻¹ * (o * w)⁻¹
        = (s * o * s⁻¹) * (s * w * s⁻¹) * w⁻¹ * o⁻¹ := by group
      _ = (s * o * s⁻¹) * o⁻¹ := by rw [hsw]; group
  rw [e]
  exact Subgroup.mul_mem _ hso (Subgroup.inv_mem _ hoO)

theorem exists_swapDiag (hF : Solomon75Frac53) (h : Sec5Data X n z Z S) (hs : IsSec5Inv X Z s)
    {A : Subgroup X} (hA : Sec5Comp X n (normalizer (Z : Set X)) A)
    (hAs : A.map (MulAut.conj s).toMonoidHom ≠ A) :
    ∃ M Δ : Subgroup X, SwapDiag X n z s M Δ := by
  classical
  have hZs : Z ≤ centralizer ({s} : Set X) := Z_le_centralizer_of_frac53 hF h hs
  have hzs : z * s = s * z := Subgroup.mem_centralizer_singleton_iff.1 (hZs h.z_mem)
  obtain ⟨M, E, hMc, hMs, -, -, -, -⟩ := exists_swapped_comp h hs hA hAs
  have hsC : s ∈ centralizer ({z} : Set X) := Subgroup.mem_centralizer_singleton_iff.2 hzs.symm
  obtain ⟨Δ, hΔle, hΔpc, hcov, -, hq⟩ := exists_diagLift hMc.isPCompIn hsC hs.sq hMs
  have hcen := cen_fixed_of_comp h hZs hsC hMc
  exact ⟨M, Δ, hMc, hzs, hMs, hΔle, hΔpc, commutator_eq_self_of_isPCompIn hΔpc,
    primeResidual_eq_top_of_isPCompIn hΔpc, hq hMc.2 hcen, hcov, hcen⟩

private theorem five_le_of_isDoubleCoverOfAlt {K : Type} [Group K]
    (h : IsDoubleCoverOfAlt K n) : 5 ≤ n := by
  by_contra hn
  push Not at hn
  obtain ⟨hq, -, ⟨e⟩⟩ := h
  have hsolv : Group.IsSolvable (alternatingGroup (Fin n)) :=
    alternatingGroup.isSolvable (by simp; omega)
  have hsolv' : Group.IsSolvable (K ⧸ center K) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  haveI : IsSimpleGroup (K ⧸ center K) := hq.2.1
  obtain ⟨a, b, hab⟩ := hq.2.2
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).2 hsolv' a b)

private theorem exists_double_transposition (hn : 4 ≤ n) :
    ∃ σ : Perm (Fin n), sign σ = 1 ∧ σ * σ = 1 ∧ fixCount σ = n - 4 := by
  obtain ⟨a, b, c, d, hab, hac, had, hbc, hbd, hcd⟩ :
      ∃ a b c d : Fin n, a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d :=
    ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩, by simp [Fin.ext_iff],
      by simp [Fin.ext_iff], by simp [Fin.ext_iff], by simp [Fin.ext_iff], by simp [Fin.ext_iff],
      by simp [Fin.ext_iff]⟩
  have hnd : [a, b, c, d].Nodup := by simp [hab, hac, had, hbc, hbd, hcd]
  have hdisj : Disjoint (swap a b) (swap c d) := Equiv.Perm.disjoint_swap_swap hnd
  refine ⟨swap a b * swap c d, ?_, ?_, ?_⟩
  · rw [Perm.sign_mul, Perm.sign_swap hab, Perm.sign_swap hcd]
    decide
  · have hc : swap c d * swap a b = swap a b * swap c d := hdisj.commute.eq.symm
    calc (swap a b * swap c d) * (swap a b * swap c d)
        = swap a b * (swap c d * swap a b) * swap c d := by simp only [mul_assoc]
      _ = swap a b * (swap a b * swap c d) * swap c d := by rw [hc]
      _ = (swap a b * swap a b) * (swap c d * swap c d) := by simp only [mul_assoc]
      _ = 1 := by rw [Equiv.swap_mul_self, Equiv.swap_mul_self, mul_one]
  · have h := fixCount_add_support (swap a b * swap c d)
    rw [hdisj.card_support_mul, Equiv.Perm.card_support_swap hab,
      Equiv.Perm.card_support_swap hcd] at h
    omega

private theorem perm_eq_of_induces_of_four_le {A : Subgroup X} (hn : 4 ≤ n)
    (M : AhatModel X n A) {c : X} (hc : c ∈ normalizer (A : Set X)) {σ : Perm (Fin n)}
    (h : M.C.Induces (M.autOf c hc) σ) : M.perm c hc = σ := by
  have hex : ∃ τ, M.C.Induces (M.autOf c hc) τ := ⟨σ, h⟩
  simp only [AhatModel.perm, hex, ↓reduceDIte]
  exact induces_unique hn hex.choose_spec h

private theorem commutator_mem_oddCoreOf_of_mk_mem_center {A : Subgroup X} {c : X} (hc : c ∈ A)
    (h : (QuotientGroup.mk (⟨c, hc⟩ : ↥A) : ↥A ⧸ pPrimeCore 2 ↥A) ∈
      center (↥A ⧸ pPrimeCore 2 ↥A)) : ∀ a ∈ A, ⁅a, c⁆ ∈ oddCoreOf A := by
  intro a ha
  have h1 := Subgroup.mem_center_iff.1 h (QuotientGroup.mk ⟨a, ha⟩)
  have h2 : (QuotientGroup.mk' (pPrimeCore 2 ↥A)) ⁅(⟨a, ha⟩ : ↥A), ⟨c, hc⟩⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2 h1
  have hmem : ⁅a, c⁆ ∈ A := by
    simp only [commutatorElement_def]
    exact A.mul_mem (A.mul_mem (A.mul_mem ha hc) (A.inv_mem ha)) (A.inv_mem hc)
  exact mem_oddCoreOf_iff.2 ⟨hmem, (QuotientGroup.eq_one_iff _).1 h2⟩

theorem mem_normalizer_of_map_normalizes_pCompIn {C M : Subgroup X} (hM : IsPCompIn 2 C M) {y : X}
    (hyC : y ∈ C)
    (hy : QuotientGroup.mk' (pPrimeCore 2 ↥C) ⟨y, hyC⟩ ∈
      normalizer (((M.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) :
        Subgroup (↥C ⧸ pPrimeCore 2 ↥C)) : Set (↥C ⧸ pPrimeCore 2 ↥C))) :
    y ∈ normalizer (M : Set X) := by
  classical
  have hMC : M ≤ C := hM.1
  set yc : ↥C := ⟨y, hyC⟩ with hyc
  have hMyC : M.map (MulAut.conj y).toMonoidHom ≤ C := by
    rintro _ ⟨x, hx, rfl⟩
    exact C.mul_mem (C.mul_mem hyC (hMC hx)) (C.inv_mem hyC)
  have hB'c : IsPComponent 2 ((M.map (MulAut.conj y).toMonoidHom).subgroupOf C) := by
    have := LocalAnalysis.ComponentInitial.isPComponent_map_of_isPComponent 2 (MulAut.conj yc) hM.2
    rwa [map_conj_subgroupOf hyC M] at this
  apply mem_normalizer_of_map_conj_eq
  have himg : ((M.map (MulAut.conj y).toMonoidHom).subgroupOf C).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥C)) =
      (M.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C)) := by
    rw [← map_conj_subgroupOf hyC M]
    have hconj : ((M.subgroupOf C).map (MulAut.conj yc).toMonoidHom).map
        (QuotientGroup.mk' (pPrimeCore 2 ↥C)) =
        ((M.subgroupOf C).map (QuotientGroup.mk' (pPrimeCore 2 ↥C))).map
          (MulAut.conj (QuotientGroup.mk' (pPrimeCore 2 ↥C) yc)).toMonoidHom := by
      rw [Subgroup.map_map, Subgroup.map_map]
      congr 1
    rw [hconj, map_conj_eq_of_mem_normalizer hy]
  have := eq_of_map_pPrimeCore_eq hB'c hM.2 himg
  rw [Subgroup.subgroupOf_inj, inf_of_le_left hMyC, inf_of_le_left hMC] at this
  exact this

private theorem sq_diag_mem_oddCoreOf {C : Subgroup X} {a u : X} (ha : a ∈ C) (hu : u ∈ C)
    (hau : ⁅a, u⁆ ∈ oddCoreOf C) (huu : u * u * (a * a)⁻¹ ∈ oddCoreOf C)
    (ha4 : (a * a) * (a * a) ∈ oddCoreOf C) : (a * u) * (a * u) ∈ oddCoreOf C := by
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  have hker : ∀ x : ↥C, π x = 1 ↔ x ∈ pPrimeCore 2 ↥C := fun x => QuotientGroup.eq_one_iff x
  have h1 : π ⟨a, ha⟩ * π ⟨u, hu⟩ = π ⟨u, hu⟩ * π ⟨a, ha⟩ := by
    have h : π ⁅(⟨a, ha⟩ : ↥C), ⟨u, hu⟩⁆ = 1 :=
      (hker _).2 ((mem_oddCoreOf_iff_subtype ⁅(⟨a, ha⟩ : ↥C), ⟨u, hu⟩⁆).1 hau)
    rw [map_commutatorElement] at h
    exact commutatorElement_eq_one_iff_mul_comm.1 h
  have h2 : π ⟨u, hu⟩ * π ⟨u, hu⟩ = π ⟨a, ha⟩ * π ⟨a, ha⟩ := by
    have h : π (⟨u, hu⟩ * ⟨u, hu⟩ * (⟨a, ha⟩ * ⟨a, ha⟩)⁻¹ : ↥C) = 1 :=
      (hker _).2
        ((mem_oddCoreOf_iff_subtype (⟨u, hu⟩ * ⟨u, hu⟩ * (⟨a, ha⟩ * ⟨a, ha⟩)⁻¹ : ↥C)).1 huu)
    rw [map_mul, map_mul, map_inv, map_mul] at h
    exact mul_inv_eq_one.1 h
  have h3 : (π ⟨a, ha⟩ * π ⟨a, ha⟩) * (π ⟨a, ha⟩ * π ⟨a, ha⟩) = 1 := by
    have h : π ((⟨a, ha⟩ * ⟨a, ha⟩) * (⟨a, ha⟩ * ⟨a, ha⟩) : ↥C) = 1 :=
      (hker _).2
        ((mem_oddCoreOf_iff_subtype ((⟨a, ha⟩ * ⟨a, ha⟩) * (⟨a, ha⟩ * ⟨a, ha⟩) : ↥C)).1 ha4)
    rw [map_mul, map_mul] at h
    exact h
  have h4 : π ((⟨a, ha⟩ * ⟨u, hu⟩) * (⟨a, ha⟩ * ⟨u, hu⟩) : ↥C) = 1 := by
    simp only [map_mul]
    calc (π ⟨a, ha⟩ * π ⟨u, hu⟩) * (π ⟨a, ha⟩ * π ⟨u, hu⟩)
        = π ⟨a, ha⟩ * (π ⟨u, hu⟩ * π ⟨a, ha⟩) * π ⟨u, hu⟩ := by group
      _ = π ⟨a, ha⟩ * (π ⟨a, ha⟩ * π ⟨u, hu⟩) * π ⟨u, hu⟩ := by rw [← h1]
      _ = (π ⟨a, ha⟩ * π ⟨a, ha⟩) * (π ⟨u, hu⟩ * π ⟨u, hu⟩) := by group
      _ = (π ⟨a, ha⟩ * π ⟨a, ha⟩) * (π ⟨a, ha⟩ * π ⟨a, ha⟩) := by rw [h2]
      _ = 1 := h3
  exact (mem_oddCoreOf_iff_subtype ((⟨a, ha⟩ * ⟨u, hu⟩) * (⟨a, ha⟩ * ⟨u, hu⟩) : ↥C)).2
    ((hker _).1 h4)

private theorem normalizes_of_diag_mod {C M : Subgroup X} (hM : IsPCompIn 2 C M)
    {a u y : X} (ha : a ∈ M) (huC : u ∈ C) (hu : ∀ m ∈ M, ⁅m, u⁆ ∈ oddCoreOf C) (hyC : y ∈ C)
    (hy : y * (a * u)⁻¹ ∈ oddCoreOf C) :
    y ∈ normalizer (M : Set X) ∧ ∀ b ∈ M, (y * b * y⁻¹)⁻¹ * (a * b * a⁻¹) ∈ oddCoreOf M := by
  classical
  have hMC : M ≤ C := hM.1
  have haC : a ∈ C := hMC ha
  set π : ↥C →* ↥C ⧸ pPrimeCore 2 ↥C := QuotientGroup.mk' (pPrimeCore 2 ↥C) with hπ
  have hker : ∀ x : ↥C, π x = 1 ↔ x ∈ pPrimeCore 2 ↥C := fun x => QuotientGroup.eq_one_iff x
  have hπy : π ⟨y, hyC⟩ = π ⟨a, haC⟩ * π ⟨u, huC⟩ := by
    have h1 : π (⟨y, hyC⟩ * (⟨a, haC⟩ * ⟨u, huC⟩)⁻¹ : ↥C) = 1 :=
      (hker _).2
        ((mem_oddCoreOf_iff_subtype (⟨y, hyC⟩ * (⟨a, haC⟩ * ⟨u, huC⟩)⁻¹ : ↥C)).1 hy)
    rw [map_mul, map_inv, map_mul] at h1
    exact mul_inv_eq_one.1 h1
  have hcomm : ∀ b : ↥C, (b : X) ∈ M → π b * π ⟨u, huC⟩ = π ⟨u, huC⟩ * π b := by
    intro b hb
    have h1 : π ⁅b, (⟨u, huC⟩ : ↥C)⁆ = 1 :=
      (hker _).2
        ((mem_oddCoreOf_iff_subtype ⁅b, (⟨u, huC⟩ : ↥C)⁆).1 (hu _ hb))
    rw [map_commutatorElement] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 h1
  have hconj : ∀ b : ↥C, (b : X) ∈ M →
      π (⟨y, hyC⟩ * b * ⟨y, hyC⟩⁻¹) = π (⟨a, haC⟩ * b * ⟨a, haC⟩⁻¹) := by
    intro b hb
    rw [map_mul, map_mul, map_inv, hπy, map_mul, map_mul, map_inv]
    have hc := hcomm b hb
    calc (π ⟨a, haC⟩ * π ⟨u, huC⟩) * π b * (π ⟨a, haC⟩ * π ⟨u, huC⟩)⁻¹
        = π ⟨a, haC⟩ * (π ⟨u, huC⟩ * π b * (π ⟨u, huC⟩)⁻¹) * (π ⟨a, haC⟩)⁻¹ := by group
      _ = π ⟨a, haC⟩ * π b * (π ⟨a, haC⟩)⁻¹ := by rw [← hc]; group
  have hnorm : y ∈ normalizer (M : Set X) := by
    refine mem_normalizer_of_map_normalizes_pCompIn hM hyC ?_
    refine mem_normalizer_of_conj_le fun x hx => ?_
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.1 hx
    have hbM : (b : X) ∈ M := hb
    refine ⟨⟨a, haC⟩ * b * ⟨a, haC⟩⁻¹, ?_, ?_⟩
    · show a * (b : X) * a⁻¹ ∈ M
      exact M.mul_mem (M.mul_mem ha hbM) (M.inv_mem ha)
    · have h1 := hconj b hbM
      rw [map_mul, map_mul, map_inv] at h1
      exact h1.symm
  refine ⟨hnorm, fun b hb => ?_⟩
  have hbC : b ∈ C := hMC hb
  have hybM : y * b * y⁻¹ ∈ M := (Subgroup.mem_normalizer_iff.1 hnorm b).1 hb
  have habM : a * b * a⁻¹ ∈ M := M.mul_mem (M.mul_mem ha hb) (M.inv_mem ha)
  have hmemM : (y * b * y⁻¹)⁻¹ * (a * b * a⁻¹) ∈ M := M.mul_mem (M.inv_mem hybM) habM
  have hπ1 : π ((⟨y, hyC⟩ * ⟨b, hbC⟩ * ⟨y, hyC⟩⁻¹)⁻¹ *
      (⟨a, haC⟩ * ⟨b, hbC⟩ * ⟨a, haC⟩⁻¹) : ↥C) = 1 := by
    rw [map_mul, map_inv, hconj ⟨b, hbC⟩ hb, inv_mul_cancel]
  have hOC : (y * b * y⁻¹)⁻¹ * (a * b * a⁻¹) ∈ oddCoreOf C :=
    (mem_oddCoreOf_iff_subtype ((⟨y, hyC⟩ * ⟨b, hbC⟩ * ⟨y, hyC⟩⁻¹)⁻¹ *
      (⟨a, haC⟩ * ⟨b, hbC⟩ * ⟨a, haC⟩⁻¹) : ↥C)).2 ((hker _).1 hπ1)
  exact inf_oddCoreOf_le hMC ⟨hmemM, hOC⟩

theorem exists_type22_involution {M Δ : Subgroup X} (hD : SwapDiag X n z s M Δ) :
    ∃ y ∈ Δ, y * y = 1 ∧ ∃ hy : y ∈ normalizer (M : Set X),
      fixCount ((AhatModel.ofCover hD.comp.2).perm y hy) = n - 4 := by
  classical
  set C : Subgroup X := centralizer ({z} : Set X) with hCdef
  have hsC : s ∈ C := Subgroup.mem_centralizer_singleton_iff.2 hD.comm.symm
  have hMp : IsPCompIn 2 C M := hD.comp.isPCompIn
  have hMC : M ≤ C := hMp.1
  have hMs : IsPCompIn 2 C (M.map (MulAut.conj s).toMonoidHom) :=
    (hD.comp.map_conj (Subgroup.le_normalizer hsC)).isPCompIn
  have hne : M ≠ M.map (MulAut.conj s).toMonoidHom := fun h => hD.moved h.symm
  have hn5 : 5 ≤ n := five_le_of_isDoubleCoverOfAlt hD.comp.2
  obtain ⟨σ₀, hσ₀sign, hσ₀sq, hσ₀fix⟩ := exists_double_transposition (n := n) (by omega)
  set Mm : AhatModel X n M := AhatModel.ofCover hD.comp.2 with hMm
  obtain ⟨k, hk⟩ := Mm.C.exists_ρ_eq hσ₀sign
  obtain ⟨m₀, hm₀⟩ := Mm.surj_mk k
  have ha : (m₀ : X) ∈ M := m₀.2
  have haC : (m₀ : X) ∈ C := hMC ha
  have hρ : Mm.C.ρ (Mm.e (QuotientGroup.mk m₀)) = σ₀ := by rw [hm₀]; exact hk
  have hk2 : Mm.e (QuotientGroup.mk m₀) * Mm.e (QuotientGroup.mk m₀) ∈ center Mm.K :=
    Mm.C.sq_mem_center (by rw [hρ, hσ₀sq])
  have hk2' : (QuotientGroup.mk (m₀ * m₀) : ↥M ⧸ pPrimeCore 2 ↥M) ∈
      center (↥M ⧸ pPrimeCore 2 ↥M) := hk2
  have hcc : ∀ x ∈ M, ⁅x, ((m₀ * m₀ : ↥M) : X)⁆ ∈ oddCoreOf M :=
    commutator_mem_oddCoreOf_of_mk_mem_center (m₀ * m₀).2 hk2'
  have hcen := hD.cen_fixed ((m₀ * m₀ : ↥M) : X) (m₀ * m₀).2 hcc
  have ha4 : ((m₀ : X) * m₀) * ((m₀ : X) * m₀) ∈ oddCoreOf C := by
    have h1 : (QuotientGroup.mk (m₀ * m₀) : ↥M ⧸ pPrimeCore 2 ↥M) *
        QuotientGroup.mk (m₀ * m₀) = 1 := Mm.C.sq_of_mem_center hk2
    have h2 : (m₀ * m₀) * (m₀ * m₀) ∈ pPrimeCore 2 ↥M := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul]
      exact h1
    exact oddCoreOf_le_of_isPCompIn hMp ((mem_oddCoreOf_iff_subtype _).2 h2)
  have huM' : s * (m₀ : X) * s⁻¹ ∈ M.map (MulAut.conj s).toMonoidHom := ⟨m₀, ha, rfl⟩
  have huC : s * (m₀ : X) * s⁻¹ ∈ C := hMs.1 huM'
  have hcommU : ∀ m ∈ M, ⁅m, s * (m₀ : X) * s⁻¹⁆ ∈ oddCoreOf C := fun m hm =>
    commutator_mem_oddCoreOf_of_ne hMp hMs hne hm huM'
  have huu : (s * (m₀ : X) * s⁻¹) * (s * (m₀ : X) * s⁻¹) * ((m₀ : X) * m₀)⁻¹ ∈ oddCoreOf C := by
    have : (s * (m₀ : X) * s⁻¹) * (s * (m₀ : X) * s⁻¹) * ((m₀ : X) * m₀)⁻¹ =
        s * ((m₀ : X) * m₀) * s⁻¹ * ((m₀ : X) * m₀)⁻¹ := by group
    rw [this]
    exact hcen
  have hy₀sq : ((m₀ : X) * (s * (m₀ : X) * s⁻¹)) * ((m₀ : X) * (s * (m₀ : X) * s⁻¹)) ∈
      oddCoreOf C := sq_diag_mem_oddCoreOf haC huC (hcommU _ ha) huu ha4
  have hy₀ : (m₀ : X) * (s * (m₀ : X) * s⁻¹) ∈ Δ ⊔ oddCoreOf C := hD.covers_diag _ ha
  have hΔC : Δ ≤ C := hD.le_cen.trans inf_le_left
  have hΔn : Δ ≤ normalizer (oddCoreOf C : Set X) := hΔC.trans (le_normalizer_oddCoreOf C)
  have hy₀C : (m₀ : X) * (s * (m₀ : X) * s⁻¹) ∈ C := C.mul_mem haC huC
  obtain ⟨o, ho, d, hdΔ, hod⟩ :=
    (CFSG.SignalizerFunctor.Helpers.mem_sup_of_normalizing (oddCoreOf C) Δ hΔn
      ((m₀ : X) * (s * (m₀ : X) * s⁻¹))).1 (by rwa [sup_comm] at hy₀)
  have hd' : d = o⁻¹ * ((m₀ : X) * (s * (m₀ : X) * s⁻¹)) := by rw [← hod]; group
  have hdd : d * d ∈ oddCoreOf C := by
    have hconj := (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf C hy₀C) o⁻¹).1
      ((oddCoreOf C).inv_mem ho)
    have e : d * d = (o⁻¹ * (((m₀ : X) * (s * (m₀ : X) * s⁻¹)) * o⁻¹ *
        ((m₀ : X) * (s * (m₀ : X) * s⁻¹))⁻¹)) *
        (((m₀ : X) * (s * (m₀ : X) * s⁻¹)) * ((m₀ : X) * (s * (m₀ : X) * s⁻¹))) := by
      rw [hd']; group
    rw [e]
    exact (oddCoreOf C).mul_mem ((oddCoreOf C).mul_mem ((oddCoreOf C).inv_mem ho) hconj) hy₀sq
  have hodd : Odd (orderOf (d * d)) := by
    have h1 := orderOf_dvd_natCard (⟨d * d, hdd⟩ : oddCoreOf C)
    rw [← Subgroup.orderOf_coe] at h1
    exact Odd.of_dvd_nat (odd_card_oddCoreOf C) h1
  obtain ⟨j, hj⟩ := hodd
  have hyΔ : d ^ (orderOf (d * d)) ∈ Δ := Subgroup.pow_mem _ hdΔ _
  have hy2 : d ^ (orderOf (d * d)) * d ^ (orderOf (d * d)) = 1 := by
    calc d ^ (orderOf (d * d)) * d ^ (orderOf (d * d)) = (d * d) ^ (orderOf (d * d)) := by
          rw [← pow_add, ← two_mul, pow_mul, sq]
      _ = 1 := pow_orderOf_eq_one _
  have hyeq : d ^ (orderOf (d * d)) = (d * d) ^ j * d := by
    rw [hj, pow_succ, pow_mul, sq]
  have hyO : d ^ (orderOf (d * d)) * ((m₀ : X) * (s * (m₀ : X) * s⁻¹))⁻¹ ∈ oddCoreOf C := by
    have h1 : d * ((m₀ : X) * (s * (m₀ : X) * s⁻¹))⁻¹ = o⁻¹ := by rw [hd']; group
    have : d ^ (orderOf (d * d)) * ((m₀ : X) * (s * (m₀ : X) * s⁻¹))⁻¹ = (d * d) ^ j * o⁻¹ := by
      rw [hyeq, mul_assoc, h1]
    rw [this]
    exact (oddCoreOf C).mul_mem (Subgroup.pow_mem _ hdd _) ((oddCoreOf C).inv_mem ho)
  obtain ⟨hynorm, hact⟩ := normalizes_of_diag_mod hMp ha huC hcommU (hΔC hyΔ) hyO
  refine ⟨d ^ (orderOf (d * d)), hyΔ, hy2, hynorm, ?_⟩
  have hauto : Mm.autOf (d ^ (orderOf (d * d))) hynorm =
      Mm.autOf (m₀ : X) (Subgroup.le_normalizer ha) := by
    refine MulEquiv.ext fun k' => ?_
    obtain ⟨b, rfl⟩ := Mm.surj_mk k'
    rw [Mm.autOf_mk, Mm.autOf_mk]
    congr 1
    refine QuotientGroup.eq.2 ?_
    exact (mem_oddCoreOf_iff_subtype _).1 (hact (b : X) b.2)
  have hind : Mm.C.Induces (Mm.autOf (d ^ (orderOf (d * d))) hynorm) σ₀ := by
    rw [hauto, Mm.autOf_of_mem ha]
    have := Mm.C.induces_conj (Mm.e (QuotientGroup.mk (⟨(m₀ : X), ha⟩ : ↥M)))
    rwa [show Mm.C.ρ (Mm.e (QuotientGroup.mk (⟨(m₀ : X), ha⟩ : ↥M))) = σ₀ from hρ] at this
  rw [perm_eq_of_induces_of_four_le (by omega) Mm hynorm hind]
  exact hσ₀fix

end DiagLift

end CFSG.OddStandard.Solomon75
