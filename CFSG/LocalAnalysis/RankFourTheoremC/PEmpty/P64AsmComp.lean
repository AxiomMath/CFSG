module

public import CFSG.LocalAnalysis.RankThreeTheoremC.RelPair2T_Struct
public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_6_8
public import CFSG.LocalAnalysis.AGLEmbedding.ReducedComponentsAux
public import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.Walter.AStar.Subnormal

public section

namespace CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GH74.Uniqueness.SU Subgroup

variable {Z : Type} [Group Z] [Finite Z] {p : ℕ}

theorem dvd_card_of_isComponentOf (hp : p.Prime) (hZ : primeComplementCore (G := Z) p = ⊥)
    {L : Subgroup Z} (hL : IsComponentOf L ⊤) : p ∣ Nat.card L := by
  by_contra hnd
  have hcop : Nat.Coprime p (Nat.card L) := (Nat.Prime.coprime_iff_not_dvd hp).2 hnd
  haveI : Fact p.Prime := ⟨hp⟩
  have hsub : L.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hL.2.1
  have hle : L ≤ CFSG.pPrimeCore p Z :=
    CFSG.LocalAnalysis.RankThreeTheoremC.ths_le_pPrimeCore_of_isSubnormal hsub hcop
  have hc : CFSG.pPrimeCore p Z = ⊥ := hZ
  rw [hc] at hle
  have hsimp := hL.2.2.2
  obtain ⟨a, b, hab⟩ := exists_pair_ne (↥L ⧸ Subgroup.center ↥L)
  have hsub1 : ∀ x y : L, x = y := by
    intro x y
    apply Subtype.ext
    have hx : (x : Z) = 1 := Subgroup.mem_bot.1 (hle x.2)
    have hy : (y : Z) = 1 := Subgroup.mem_bot.1 (hle y.2)
    rw [hx, hy]
  obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
  rw [hsub1 a' b'] at hab
  exact hab rfl

theorem dvd_card_quotient_center {K : Type} [Group K] [Finite K] (hK : Open.IsQuasisimple K)
    (hp : p.Prime) (hp2 : p ≠ 2) (hdvd : p ∣ Nat.card K) :
    p ∣ Nat.card (K ⧸ Subgroup.center K) := by
  obtain ⟨x, hxo, hxc⟩ :=
    CFSG.HardMathSupport.Timmesfeld.ComponentBalance.exists_orderOf_eq_prime_not_mem_center
      hK hp hp2 hdvd
  have hdvd1 : orderOf (x : K ⧸ Subgroup.center K) ∣ orderOf x :=
    orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center K)) x
  rw [hxo] at hdvd1
  have hne : (x : K ⧸ Subgroup.center K) ≠ 1 := by
    rw [Ne, QuotientGroup.eq_one_iff]
    exact hxc
  have hord : orderOf (x : K ⧸ Subgroup.center K) ≠ 1 := by
    rw [Ne, orderOf_eq_one_iff]
    exact hne
  have h3 : orderOf (x : K ⧸ Subgroup.center K) = p := by
    rcases hp.eq_one_or_self_of_dvd _ hdvd1 with h | h
    · exact absurd h hord
    · exact h
  have hfin := orderOf_dvd_natCard (x : K ⧸ Subgroup.center K)
  rwa [h3] at hfin

theorem exists_mem_inf_sylow_component (hp : p.Prime) (hp2 : p ≠ 2)
    (hZ : primeComplementCore (G := Z) p = ⊥) (Q : Sylow p Z) {L : Subgroup Z}
    (hL : IsComponentOf L ⊤) :
    ∃ y ∈ (Q : Subgroup Z) ⊓ L, orderOf y = p ∧ ∃ l ∈ L, l * y ≠ y * l := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsub : L.IsSubnormal := CFSG.Open.IsSubnormal.top_iff.1 hL.2.1
  obtain ⟨P, hP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal Q hsub
  have hdvd : p ∣ Nat.card (↥L ⧸ Subgroup.center ↥L) :=
    dvd_card_quotient_center hL.2.2 hp hp2 (dvd_card_of_isComponentOf hp hZ hL)
  obtain ⟨t, htP, hto, htc⟩ :=
    CFSG.AGLEmbedding.exists_mem_sylow_orderOf_eq_not_mem_center hp hp2 hL.2.2 hdvd P
  refine ⟨(t : Z), ?_, ?_, ?_⟩
  · rw [← hP]
    exact Subgroup.mem_map_of_mem L.subtype htP
  · rw [Subgroup.orderOf_coe, hto]
  · obtain ⟨g, hg⟩ : ∃ g : L, g * t ≠ t * g := by
      by_contra hcon
      push Not at hcon
      exact htc (Subgroup.mem_center_iff.2 fun g => hcon g)
    exact ⟨(g : Z), g.2, fun h => hg (Subtype.ext h)⟩

theorem isComponentOf_map_conj {L : Subgroup Z} (hL : IsComponentOf L ⊤) (g : Z) :
    IsComponentOf (L.map (MulAut.conj g).toMonoidHom) ⊤ := by
  have hsurj : Function.Surjective (MulAut.conj g).toMonoidHom := (MulAut.conj g).surjective
  have hinj : Function.Injective (MulAut.conj g).toMonoidHom := (MulAut.conj g).injective
  refine ⟨le_top, ?_, ?_⟩
  · have h := CFSG.Open.IsSubnormal.map (MulAut.conj g).toMonoidHom hL.2.1
    rwa [Subgroup.map_top_of_surjective _ hsurj] at h
  · exact CFSG.Open.IsQuasisimple.of_mulEquiv
      (L.equivMapOfInjective (MulAut.conj g).toMonoidHom hinj).symm hL.2.2

theorem component_commute {L₁ L₂ : Subgroup Z} (h₁ : IsComponentOf L₁ ⊤)
    (h₂ : IsComponentOf L₂ ⊤) (h12 : L₁ ≠ L₂) {a b : Z} (ha : a ∈ L₁) (hb : b ∈ L₂) :
    a * b = b * a := by
  have hcomm := CFSG.ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ h₁ h₂ h12
  have hmem := Subgroup.commutator_mem_commutator ha hb
  rw [hcomm, Subgroup.mem_bot] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hmem

theorem isElemAbelian_card_sup_zpowers_of_card {G : Type*} [Group G] [Finite G] (hp : p.Prime)
    {E : Subgroup G} {k : ℕ} (hE : IsElemAbelian p E) (hEk : Nat.card E = p ^ k) {y : G}
    (hy : y ^ p = 1) (hyE : y ∉ E) (hcomm : ∀ e ∈ E, e * y = y * e) :
    IsElemAbelian p (E ⊔ zpowers y) ∧ Nat.card (E ⊔ zpowers y : Subgroup G) = p ^ (k + 1) := by
  have := Fact.mk hp
  have hcomm' : ∀ s ∈ E, ∀ t ∈ zpowers y, s * t = t * s := by
    rintro s hs t ⟨n, rfl⟩
    exact (Commute.zpow_right (show Commute s y from hcomm s hs) n).eq
  have hel : IsElemAbelian p (E ⊔ zpowers y) :=
    SU1.IsElemAbelian.sup hE (SU1.isElemAbelian_zpowers hy) hcomm'
  refine ⟨hel, ?_⟩
  have hy1 : y ≠ 1 := fun h => hyE (h ▸ one_mem _)
  have hoy : orderOf y = p := orderOf_eq_prime hy hy1
  have hup : Nat.card (E ⊔ zpowers y : Subgroup G) ≤ p ^ k * p := by
    refine (SU1.card_sup_le_of_commute hcomm').trans ?_
    rw [Nat.card_zpowers, hoy, hEk]
  have hlt : E < E ⊔ zpowers y :=
    lt_of_le_of_ne le_sup_left (fun h => hyE (h ▸ Subgroup.mem_sup_right (mem_zpowers y)))
  have hcl := SU1.card_lt_of_lt hlt
  obtain ⟨m, hm⟩ := SU1.IsElemAbelian.exists_card hp hel
  rw [hEk, hm] at hcl
  rw [hm] at hup ⊢
  have hkm : k < m := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hcl
  have hmk : m ≤ k + 1 := by
    have : p ^ m ≤ p ^ (k + 1) := by rw [pow_succ]; exact hup
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp this
  have : m = k + 1 := by omega
  rw [this]

theorem exists_cube_containing_central (hp : p.Prime) {Q : Subgroup Z} (h3 : 3 ≤ Open.pRank p Q)
    {y : Z} (hyQ : y ∈ Q) (hyp : y ^ p = 1) (hyc : ∀ q ∈ Q, q * y = y * q) :
    ∃ E : Subgroup Z, E ≤ Q ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 3 ∧ y ∈ E := by
  obtain ⟨E₀, hE₀Q, hE₀, hE₀c⟩ := SU1.exists_isElemAbelian_of_le_pRank hp h3
  by_cases hy : y ∈ E₀
  · exact ⟨E₀, hE₀Q, hE₀, hE₀c, hy⟩
  · obtain ⟨F, hFE, hF, hFc⟩ := SU1.exists_subgroup_card hp hE₀ (j := 2) (by norm_num) hE₀c
    have hyF : y ∉ F := fun h => hy (hFE h)
    obtain ⟨hel, hcard⟩ := isElemAbelian_card_sup_zpowers_of_card hp hF hFc hyp hyF
      (fun e he => hyc e (hE₀Q (hFE he)))
    refine ⟨F ⊔ zpowers y, sup_le (hFE.trans hE₀Q) (zpowers_le.mpr hyQ), hel, hcard,
      Subgroup.mem_sup_right (mem_zpowers y)⟩

theorem isElemAbelian_card_two_of_components (hp : p.Prime) {L₁ L₂ : Subgroup Z}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (h12 : L₁ ≠ L₂) {y₁ y₂ : Z}
    (hy₁ : y₁ ∈ L₁) (hy₂ : y₂ ∈ L₂) (hp₁ : y₁ ^ p = 1) (hp₂ : y₂ ^ p = 1)
    (hc₁ : ∃ l ∈ L₁, l * y₁ ≠ y₁ * l) (hc₂ : ∃ l ∈ L₂, l * y₂ ≠ y₂ * l) :
    IsElemAbelian p (zpowers y₁ ⊔ zpowers y₂) ∧
      Nat.card (zpowers y₁ ⊔ zpowers y₂ : Subgroup Z) = p ^ 2 := by
  have hy11 : y₁ ≠ 1 := by
    rintro rfl
    obtain ⟨l, -, hl⟩ := hc₁
    exact hl (by simp)
  have hy₂z : y₂ ∉ zpowers y₁ := by
    intro hmem
    obtain ⟨l, hl, hne⟩ := hc₂
    have hy₂₁ : y₂ ∈ L₁ := zpowers_le.mpr hy₁ hmem
    exact hne (component_commute h₂ h₁ h12.symm hl hy₂₁)
  exact SU1.isElemAbelian_card_sup_zpowers hp hp₁ hp₂ hy11 hy₂z
    (component_commute h₁ h₂ h12 hy₁ hy₂)

theorem isElemAbelian_card_three_of_components (hp : p.Prime) {L₁ L₂ L₃ : Subgroup Z}
    (h₁ : IsComponentOf L₁ ⊤) (h₂ : IsComponentOf L₂ ⊤) (h₃ : IsComponentOf L₃ ⊤)
    (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) {y₁ y₂ y₃ : Z}
    (hy₁ : y₁ ∈ L₁) (hy₂ : y₂ ∈ L₂) (hy₃ : y₃ ∈ L₃) (hp₁ : y₁ ^ p = 1) (hp₂ : y₂ ^ p = 1)
    (hp₃ : y₃ ^ p = 1) (hc₁ : ∃ l ∈ L₁, l * y₁ ≠ y₁ * l) (hc₂ : ∃ l ∈ L₂, l * y₂ ≠ y₂ * l)
    (hc₃ : ∃ l ∈ L₃, l * y₃ ≠ y₃ * l) :
    IsElemAbelian p (zpowers y₁ ⊔ zpowers y₂ ⊔ zpowers y₃) ∧
      Nat.card (zpowers y₁ ⊔ zpowers y₂ ⊔ zpowers y₃ : Subgroup Z) = p ^ 3 := by
  obtain ⟨hel, hcard⟩ := isElemAbelian_card_two_of_components hp h₁ h₂ h12 hy₁ hy₂ hp₁ hp₂ hc₁ hc₂
  have hcent : zpowers y₁ ⊔ zpowers y₂ ≤ centralizer (L₃ : Set Z) := by
    refine sup_le ?_ ?_
    · rw [zpowers_le, mem_centralizer_iff]
      intro g hg
      exact (component_commute h₁ h₃ h13 hy₁ hg).symm
    · rw [zpowers_le, mem_centralizer_iff]
      intro g hg
      exact (component_commute h₂ h₃ h23 hy₂ hg).symm
  have hy₃E : y₃ ∉ zpowers y₁ ⊔ zpowers y₂ := by
    intro hmem
    obtain ⟨l, hl, hne⟩ := hc₃
    have := (mem_centralizer_iff.mp (hcent hmem)) l hl
    exact hne this
  refine isElemAbelian_card_sup_zpowers_of_card hp hel hcard hp₃ hy₃E ?_
  intro e he
  have := (mem_centralizer_iff.mp (hcent he)) y₃ hy₃
  exact this.symm

end CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Asm
