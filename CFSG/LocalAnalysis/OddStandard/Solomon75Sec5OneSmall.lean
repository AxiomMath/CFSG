module

public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneJhat
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5CentMirror
public import CFSG.LocalAnalysis.OddStandard.Solomon75Sec5OneSetup

public section

namespace CFSG.OddStandard.Solomon75

open Equiv Equiv.Perm Subgroup CFSG CFSG.GH74.GLS
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X] {n : ℕ} {z : X} {Z : Subgroup X}
  {S : Sylow 2 ↥(normalizer (Z : Set X))} {s : X}

omit [Finite X] in
theorem exists_support_card_of_mul_self {m : ℕ} {σ : Perm (Fin m)} (h : σ * σ = 1) :
    ∃ k, σ.support.card = 2 * k := by
  have hpow : σ ^ 2 = 1 := by rw [pow_two, h]
  have hrep := Equiv.Perm.cycleType_of_pow_prime_eq_one hpow
  have hsum := Equiv.Perm.sum_cycleType σ
  rw [hrep, Multiset.sum_replicate, smul_eq_mul] at hsum
  exact ⟨σ.cycleType.card, by omega⟩

theorem Sec5S.exists_k (hS : Sec5S X n z Z S s) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) (M : AhatModel X n A) :
    M.perm s (hS.norm A hA) * M.perm s (hS.norm A hA) = 1 ∧
      ∃ k, 4 ≤ k ∧ (M.perm s (hS.norm A hA)).support.card = 2 * k := by
  have hn : 8 ≤ n := hS.data.maxdeg.1
  have hsA := hS.norm A hA
  have hsq : M.perm s hsA * M.perm s hsA = 1 := by
    have : (⟨s, hsA⟩ : ↥(normalizer (A : Set X))) * ⟨s, hsA⟩ = 1 := Subtype.ext hS.inv.sq
    have h1 := congrArg (M.permHom hn) this
    rwa [map_mul, map_one] at h1
  refine ⟨hsq, ?_⟩
  obtain ⟨k, hk⟩ := exists_support_card_of_mul_self hsq
  obtain ⟨hf, hk3⟩ := hS.frac A hA hsA M
  have hadd := fixCount_add_support (M.perm s hsA)
  have hk' : transCount (M.perm s hsA) = k := by
    unfold transCount; rw [hk]; omega
  rw [hk'] at hk3
  refine ⟨k, ?_, hk⟩
  omega

theorem Sec5S.exists_jhat_comp (hS : Sec5S X n z Z S s) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) :
    ∃ J : Subgroup (↥A ⧸ pPrimeCore 2 ↥A),
      J ≤ AhatData.fixSub ((AhatModel.ofCover hA.2).autOf s (hS.norm A hA)) ∧
        Nat.card ↥J = 64 ∧ Nat.card ↥(Subgroup.center ↥J) ≤ 4 ∧
        J ≤ Subgroup.closure {x | x ∈ J ∧ x * x = 1} := by
  have hn : 8 ≤ n := hS.data.maxdeg.1
  obtain ⟨hσ, k, hk4, hk⟩ := hS.exists_k hA (AhatModel.ofCover hA.2)
  exact exists_jhat (K := ↥A ⧸ pPrimeCore 2 ↥A) hn (AhatModel.ofCover hA.2).C
    ((AhatModel.ofCover hA.2).induces_perm hn s (hS.norm A hA)) hσ hk hk4

theorem Sec5S.exists_two_group (hS : Sec5S X n z Z S s) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) :
    ∃ V : Subgroup X, V ≤ hGrp s A ∧ IsPGroup 2 ↥V ∧ Nat.card ↥V = 64 ∧
      Nat.card ↥(Subgroup.center ↥V) ≤ 4 := by
  have hfact : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsA := hS.norm A hA
  obtain ⟨J, hJfix, hJ64, hJc, hJgen⟩ := hS.exists_jhat_comp hA
  set q : ↥A →* ↥A ⧸ pPrimeCore 2 ↥A := QuotientGroup.mk' (pPrimeCore 2 ↥A) with hq
  set H : Subgroup ↥A := (hGrp s A).subgroupOf A with hH
  have hJH : J ≤ H.map q := by
    refine hJgen.trans ((Subgroup.closure_le _).2 ?_)
    rintro x ⟨hxJ, hx2⟩
    by_cases hx1 : x = 1
    · rw [hx1]; exact one_mem _
    · obtain ⟨r, hr, hrA, hrx⟩ :=
        exists_inv_lift hA.2 hsA hS.inv.sq (AhatData.mem_fixSub.1 (hJfix hxJ)) hx2 hx1
      exact ⟨⟨r, hrA⟩, Subgroup.mem_subgroupOf.2 (subset_hGrp hr), hrx⟩
  set U : Subgroup ↥A := J.comap q ⊓ H with hU
  let q' : ↥U →* ↥J := (q.comp U.subtype).codRestrict J (fun u => u.2.1)
  have hq'surj : Function.Surjective q' := by
    rintro ⟨x, hx⟩
    obtain ⟨u, hu, hux⟩ := hJH hx
    exact ⟨⟨u, Subgroup.mem_comap.2 (hux ▸ hx), hu⟩, Subtype.ext hux⟩
  have hkerodd : Odd (Nat.card q'.ker) := by
    have hinj : Function.Injective
        (fun u : q'.ker => (⟨(u.1 : ↥A), by
          have h1 := congrArg Subtype.val (MonoidHom.mem_ker.1 u.2)
          exact (QuotientGroup.eq_one_iff _).1 h1⟩ : ↥(pPrimeCore 2 ↥A))) := by
      intro a b hab
      exact Subtype.ext (Subtype.ext (congrArg (fun w : ↥(pPrimeCore 2 ↥A) => (w : ↥A)) hab))
    have hdvd : Nat.card q'.ker ∣ Nat.card (pPrimeCore 2 ↥A) := by
      let f : q'.ker →* ↥(pPrimeCore 2 ↥A) :=
        { toFun := fun u => ⟨(u.1 : ↥A), by
            have h1 := congrArg Subtype.val (MonoidHom.mem_ker.1 u.2)
            exact (QuotientGroup.eq_one_iff _).1 h1⟩
          map_one' := rfl
          map_mul' := fun a b => rfl }
      exact Subgroup.card_dvd_of_injective f hinj
    exact Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_right hdvd pPrimeCore_coprime_card)
  have hcardU : Nat.card U = Nat.card q'.ker * 64 := by
    have h1 := Subgroup.card_ker_mul_card_range q'
    rw [MonoidHom.range_eq_top.2 hq'surj, Subgroup.card_top, hJ64] at h1
    exact h1.symm
  obtain ⟨P⟩ : Nonempty (Sylow 2 ↥U) := inferInstance
  have hcardP : Nat.card P = 64 := by
    have hpos : Nat.card q'.ker ≠ 0 := Nat.card_pos.ne'
    have h0 : (Nat.card q'.ker).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro h2; exact (Nat.not_even_iff_odd.2 hkerodd) (even_iff_two_dvd.2 h2))
    have h64 : (64 : ℕ).factorization 2 = 6 := by
      rw [show (64 : ℕ) = 2 ^ 6 by norm_num, Nat.Prime.factorization_pow Nat.prime_two]
      simp
    rw [Sylow.card_eq_multiplicity, hcardU, Nat.factorization_mul hpos (by norm_num),
      Finsupp.add_apply, h0, h64]
    norm_num
  have hPinj : Function.Injective (q'.comp (P : Subgroup ↥U).subtype) := by
    rw [injective_iff_map_eq_one]
    intro p hp
    have hker : (p : ↥U) ∈ q'.ker := hp
    exact Subtype.ext (eq_one_of_mem_of_mem_odd q'.ker (P : Subgroup ↥U) hkerodd P.isPGroup' p.2
      hker)
  have hPbij : Function.Bijective (q'.comp (P : Subgroup ↥U).subtype) :=
    hPinj.bijective_of_nat_card_le (by rw [hcardP, hJ64])
  let e : ↥(P : Subgroup ↥U) ≃* ↥J := MulEquiv.ofBijective _ hPbij
  have hcenP : Nat.card ↥(Subgroup.center ↥(P : Subgroup ↥U)) ≤ 4 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv]; exact hJc
  set V : Subgroup X := ((P : Subgroup ↥U).map U.subtype).map A.subtype with hV
  have hVU : V ≤ hGrp s A := by
    rintro _ ⟨_, ⟨u, hu, rfl⟩, rfl⟩
    exact Subgroup.mem_subgroupOf.1 u.2.2
  let eV : ↥(P : Subgroup ↥U) ≃* ↥V :=
    (Subgroup.equivMapOfInjective _ U.subtype U.subtype_injective).trans
      (Subgroup.equivMapOfInjective _ A.subtype A.subtype_injective)
  refine ⟨V, hVU, ?_, ?_, ?_⟩
  · exact IsPGroup.of_equiv P.isPGroup' eV
  · rw [← Nat.card_congr eV.toEquiv]; exact hcardP
  · rw [← Nat.card_congr (Subgroup.centerCongr eV).toEquiv]; exact hcenP

theorem Sec5S.eq_one_of_mem_two_group (hS : Sec5S X n z Z S s) (hn : 8 ≤ n) {B : Subgroup X}
    (hB : Sec5Comp X n (centralizer ({s} : Set X)) B) (M : AhatModel X n B) {A : Subgroup X}
    (hA : Sec5Comp X n (normalizer (Z : Set X)) A) {V : Subgroup X} (hV : V ≤ hGrp s A)
    (hV2 : IsPGroup 2 ↥V) {w : X} (hwV : w ∈ V) (hwN : w ∈ normComps X n s)
    (hw : pAct hn hB M ⟨w, hwN⟩ = 1) : w = 1 := by
  have hVN : V ≤ normComps X n s := hV.trans (hS.hGrp_le_normComps hA)
  have hV'2 : IsPGroup 2 ↥(V.subgroupOf (normComps X n s)) :=
    hV2.of_equiv (Subgroup.subgroupOfEquivOfLe hVN).symm
  have h1 := eq_one_of_mem_of_mem_odd
    ((hGrp s A).subgroupOf (normComps X n s) ⊓ (pAct hn hB M).ker) (V.subgroupOf (normComps X n s))
    (hS.odd_card_hGrp_inf_ker hn hB M hA) hV'2 (x := ⟨w, hwN⟩) hwV
    ⟨hV hwV, MonoidHom.mem_ker.2 hw⟩
  exact congrArg Subtype.val h1

theorem Sec5S.small_false (hS : Sec5S X n z Z S s) (hn11 : n ≤ 11) {A₁ A₂ : Subgroup X}
    (hA₁ : Sec5Comp X n (normalizer (Z : Set X)) A₁)
    (hA₂ : Sec5Comp X n (normalizer (Z : Set X)) A₂) (hne : A₁ ≠ A₂) : False := by
  have hn : 8 ≤ n := hS.data.maxdeg.1
  obtain ⟨B, hB, -⟩ := hS.data.exists_comp_centralizer hS.inv
  set M : AhatModel X n B := AhatModel.ofCover hB.2 with hM
  set N : Subgroup X := normalizer (Z : Set X) with hN
  set G : Subgroup X := normComps X n s ⊓ N with hG
  let p : ↥(normComps X n s) →* Perm (Fin n) := pAct hn hB M
  let p₀ : ↥G →* Perm (Fin n) := p.comp (Subgroup.inclusion inf_le_left)
  let Q : Subgroup (Perm (Fin n)) := p₀.range
  let pb : ↥G →* ↥Q := p₀.rangeRestrict
  have hpb : Function.Surjective pb := p₀.rangeRestrict_surjective
  have hpbapp : ∀ g : ↥G, ((pb g : ↥Q) : Perm (Fin n)) = p₀ g := fun g => rfl
  obtain ⟨V₁, hV₁, hV₁2, hV₁c, hV₁z⟩ := hS.exists_two_group hA₁
  obtain ⟨V₂, hV₂, hV₂2, hV₂c, hV₂z⟩ := hS.exists_two_group hA₂
  have hVG : ∀ (A : Subgroup X), Sec5Comp X n N A → ∀ (V : Subgroup X), V ≤ hGrp s A → V ≤ G := by
    intro A hA V hV
    exact le_inf (hV.trans (hS.hGrp_le_normComps hA))
      (((hV.trans (hGrp_le _ _)).trans inf_le_left).trans hA.isPCompIn.1)
  have key : ∀ (A : Subgroup X), Sec5Comp X n N A → ∀ (V : Subgroup X), V ≤ hGrp s A →
      IsPGroup 2 ↥V → Function.Injective (pb.comp (V.subgroupOf G).subtype) := by
    intro A hA V hV hV2
    rw [injective_iff_map_eq_one]
    intro w hw
    have hw0 : p₀ (w : ↥G) = 1 := by
      have := congrArg Subtype.val hw
      simpa [hpbapp] using this
    have := hS.eq_one_of_mem_two_group hn hB M hA hV hV2 (w := ((w : ↥G) : X)) w.2
      (w : ↥G).2.1 hw0
    exact Subtype.ext (Subtype.ext this)
  have hinj₁ := key A₁ hA₁ V₁ hV₁ hV₁2
  have hinj₂ := key A₂ hA₂ V₂ hV₂ hV₂2
  let r₁ : ↥(V₁.subgroupOf G) →* ↥Q := pb.comp (V₁.subgroupOf G).subtype
  let r₂ : ↥(V₂.subgroupOf G) →* ↥Q := pb.comp (V₂.subgroupOf G).subtype
  let e₁ : ↥V₁ ≃* ↥r₁.range := (Subgroup.subgroupOfEquivOfLe (hVG A₁ hA₁ V₁ hV₁)).symm.trans
    (MonoidHom.ofInjective hinj₁)
  let e₂ : ↥V₂ ≃* ↥r₂.range := (Subgroup.subgroupOfEquivOfLe (hVG A₂ hA₂ V₂ hV₂)).symm.trans
    (MonoidHom.ofInjective hinj₂)
  have hc₁ : Nat.card r₁.range = 64 := by rw [← Nat.card_congr e₁.toEquiv]; exact hV₁c
  have hc₂ : Nat.card r₂.range = 64 := by rw [← Nat.card_congr e₂.toEquiv]; exact hV₂c
  have hp₁ : IsPGroup 2 ↥r₁.range := hV₁2.of_equiv e₁
  have hp₂ : IsPGroup 2 ↥r₂.range := hV₂2.of_equiv e₂
  have hz₁ : Nat.card ↥(Subgroup.center ↥r₁.range) ≤ 4 := by
    rw [← Nat.card_congr (Subgroup.centerCongr e₁).toEquiv]; exact hV₁z
  let Y : Subgroup ↥G := (oddCoreOf N).subgroupOf G
  have hYn : Y.Normal := ⟨fun a ha g => by
    show ((g * a * g⁻¹ : ↥G) : X) ∈ oddCoreOf N
    have hg : (g : X) ∈ N := g.2.2
    have h1 : (a : X) ∈ oddCoreOf N := ha
    have := (Subgroup.mem_normalizer_iff.1 (le_normalizer_oddCoreOf N hg) (a : X)).1 h1
    simpa using this⟩
  let L : Subgroup ↥Q := Y.map pb
  have : L.Normal := Subgroup.Normal.map hYn pb hpb
  have hLodd : Odd (Nat.card L) := by
    have hYle : Y.map G.subtype ≤ oddCoreOf N := by
      rintro _ ⟨y, hy, rfl⟩
      exact hy
    have h0 : Nat.card (Y.map G.subtype) = Nat.card Y :=
      Subgroup.card_map_of_injective G.subtype_injective
    have h1 : Nat.card Y ∣ Nat.card (oddCoreOf N) := by
      rw [← h0]
      exact Subgroup.card_dvd_of_le hYle
    exact Odd.of_dvd_nat (odd_card_oddCoreOf N) ((Subgroup.card_map_dvd Y pb).trans h1)
  have hcomm : ∀ a ∈ r₁.range, ∀ b ∈ r₂.range, ⁅a, b⁆ ∈ L := by
    rintro _ ⟨w₁, rfl⟩ _ ⟨w₂, rfl⟩
    refine ⟨⁅((w₁ : ↥(V₁.subgroupOf G)) : ↥G), ((w₂ : ↥(V₂.subgroupOf G)) : ↥G)⁆, ?_,
      map_commutatorElement pb _ _⟩
    show ((⁅((w₁ : ↥(V₁.subgroupOf G)) : ↥G), ((w₂ : ↥(V₂.subgroupOf G)) : ↥G)⁆ : ↥G) : X) ∈
      oddCoreOf N
    have ha : ((w₁ : ↥(V₁.subgroupOf G)) : X) ∈ A₁ := (hGrp_le s A₁ (hV₁ w₁.2)).1
    have hb : ((w₂ : ↥(V₂.subgroupOf G)) : X) ∈ A₂ := (hGrp_le s A₂ (hV₂ w₂.2)).1
    have := commutator_mem_oddCoreOf_of_ne hA₁.isPCompIn hA₂.isPCompIn hne ha hb
    simpa [commutatorElement_def] using this
  have h2 := card_mul_le_two_part_of_comm_mod L hLodd r₁.range r₂.range hp₁ hp₂ hcomm
  rw [hc₁, hc₂] at h2
  have h3 := two_pow_factorization_card_le hn11 Q
  have h4 : 64 * 64 ≤ 256 * 4 := h2.trans (Nat.mul_le_mul h3 hz₁)
  omega

end CFSG.OddStandard.Solomon75
