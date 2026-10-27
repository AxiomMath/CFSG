module

public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PrimeComplementCore

public section

open CFSG.Open CFSG.LocalAnalysis.GLTheoremB CFSG.HardMathSupport.Solomon.LocalBalance
  CFSG.HardMathSupport.Solomon.LocalBalance.Lemma512Ns
open CFSG.RankThreeCoreUniqueness.Helpers (primeComplementCore)

namespace CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44Data

section Comp

variable {K : Type} [Group K] [Finite K] {X J J₁ J₂ : Subgroup K}

theorem card_barX_eq_sixty (hJ : GLAPComponent 5 X J)
    (hA : Nonempty (↥J ⧸ primeComplementCore (G := ↥J) 5 ≃* alternatingGroup (Fin 5))) :
    Nat.card ↥(barX 5 X J) = 60 := by
  obtain ⟨e⟩ := hA
  have h1 := barXEquiv Nat.prime_five hJ.2.1
  rw [← Nat.card_congr h1.toEquiv]
  have h2 : Nat.card (barOf 5 J) = Nat.card (alternatingGroup (Fin 5)) :=
    Nat.card_congr e.toEquiv
  rw [h2, Nat.card_eq_fintype_card, card_alternatingGroup]
  decide

theorem barX_center_trivial (hJ : GLAPComponent 5 X J)
    (hA : Nonempty (↥J ⧸ primeComplementCore (G := ↥J) 5 ≃* alternatingGroup (Fin 5))) :
    Subgroup.center ↥(barX 5 X J) = ⊥ := by
  obtain ⟨e⟩ := hA
  have h1 := barXEquiv Nat.prime_five hJ.2.1
  have e' : ↥(barX 5 X J) ≃* alternatingGroup (Fin 5) := h1.symm.trans e
  have hc : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  rw [← Subgroup.map_center_eq e'.symm, hc, Subgroup.map_bot]

theorem nine_dvd_card_of_two_components
    (h₁ : GLAPComponent 5 X J₁) (h₂ : GLAPComponent 5 X J₂) (hne : J₁ ≠ J₂)
    (hA₁ : Nonempty (↥J₁ ⧸ primeComplementCore (G := ↥J₁) 5 ≃* alternatingGroup (Fin 5)))
    (hA₂ : Nonempty (↥J₂ ⧸ primeComplementCore (G := ↥J₂) 5 ≃* alternatingGroup (Fin 5))) :
    9 ∣ Nat.card ↥X := by
  have hne' : barX 5 X J₁ ≠ barX 5 X J₂ := fun h => hne (glaPComponent_uniqueAux h₁ h₂ h)
  have hcomm : ⁅barX 5 X J₁, barX 5 X J₂⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁.2.2.1 h₂.2.2.1 hne'
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hc : ∀ (m : ↥(barX 5 X J₁)) (n : ↥(barX 5 X J₂)),
      Commute ((barX 5 X J₁).subtype m) ((barX 5 X J₂).subtype n) := by
    intro m n
    have := Subgroup.mem_centralizer_iff.mp (hle m.2) n n.2
    exact this.symm
  have hinj := (MonoidHom.noncommCoprod_injective (barX 5 X J₁).subtype (barX 5 X J₂).subtype
    hc).mpr ⟨Subgroup.subtype_injective _, Subgroup.subtype_injective _, by
      rw [Subgroup.range_subtype, Subgroup.range_subtype, Subgroup.disjoint_def]
      intro z hz₁ hz₂
      have hz : (⟨z, hz₁⟩ : ↥(barX 5 X J₁)) ∈ Subgroup.center ↥(barX 5 X J₁) := by
        rw [Subgroup.mem_center_iff]
        intro w
        exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hle w.2) z hz₂).symm
      rw [barX_center_trivial h₁ hA₁, Subgroup.mem_bot] at hz
      exact congrArg Subtype.val hz⟩
  have h3600 := Subgroup.card_dvd_of_injective _ hinj
  rw [Nat.card_prod, card_barX_eq_sixty h₁ hA₁, card_barX_eq_sixty h₂ hA₂] at h3600
  have h4 := Subgroup.card_quotient_dvd_card (GLAPPrimeCore 5 ↥X)
  exact (show 9 ∣ 60 * 60 by norm_num).trans (h3600.trans h4)

theorem exists_fixed_mul_normal {G : Type*} [Group G] [Finite G] (N : Subgroup G) [hN : N.Normal]
    (hcop : Nat.Coprime 5 (Nat.card N)) {a : G} (ha : a ^ 5 = 1) {j : G}
    (hj : j⁻¹ * a * j * a⁻¹ ∈ N) :
    ∃ z : G, j⁻¹ * z ∈ N ∧ a * z * a⁻¹ = z := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  let S : Type _ := {z : G // j⁻¹ * z ∈ N}
  have hmem : ∀ z : S, j⁻¹ * (a * z.1 * a⁻¹) ∈ N := by
    intro z
    have h1 : j⁻¹ * (a * z.1 * a⁻¹) = (j⁻¹ * a * j * a⁻¹) * (a * (j⁻¹ * z.1) * a⁻¹) := by group
    rw [h1]
    exact N.mul_mem hj (hN.conj_mem _ z.2 a)
  let f : S → S := fun z => ⟨a * z.1 * a⁻¹, hmem z⟩
  have hf : Function.Injective f := by
    intro z w h
    apply Subtype.ext
    have := congrArg Subtype.val h
    simpa [f] using this
  let σ : Equiv.Perm S := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf)
  have hσ : ∀ (n : ℕ) (z : S), ((σ ^ n) z).1 = a ^ n * z.1 * (a ^ n)⁻¹ := by
    intro n
    induction n with
    | zero => intro z; simp
    | succ n ih =>
      intro z
      rw [pow_succ, Equiv.Perm.mul_apply, ih]
      show a ^ n * (a * z.1 * a⁻¹) * (a ^ n)⁻¹ = a ^ (n + 1) * z.1 * (a ^ (n + 1))⁻¹
      rw [pow_succ', mul_inv_rev]
      group
  have hσ5 : σ ^ (5 ^ 1) = 1 := by
    ext z
    rw [pow_one, hσ, ha]
    simp
  let eS : S ≃ N := ⟨fun z => ⟨j⁻¹ * z.1, z.2⟩, fun n => ⟨j * n.1, by simpa using n.2⟩,
    fun z => by simp, fun n => by simp⟩
  letI : Fintype S := Fintype.ofFinite S
  have hcard : ¬ 5 ∣ Fintype.card S := by
    rw [← Nat.card_eq_fintype_card, Nat.card_congr eS]
    intro h
    have := Nat.Coprime.eq_one_of_dvd hcop h
    omega
  obtain ⟨z, hz⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 5) (n := 1) hcard hσ5
  exact ⟨z.1, z.2, congrArg Subtype.val hz⟩

theorem sixty_dvd_card_inf_centralizer
    (h₁ : GLAPComponent 5 X J₁) (h₂ : GLAPComponent 5 X J₂) (hne : J₁ ≠ J₂)
    (hA₂ : Nonempty (↥J₂ ⧸ primeComplementCore (G := ↥J₂) 5 ≃* alternatingGroup (Fin 5)))
    {a : K} (ha : a ∈ J₁) (ha5 : a ^ 5 = 1) :
    60 ∣ Nat.card ↥(X ⊓ Subgroup.centralizer ({a} : Set K)) := by
  have hne' : barX 5 X J₁ ≠ barX 5 X J₂ := fun h => hne (glaPComponent_uniqueAux h₁ h₂ h)
  have hcomm : ⁅barX 5 X J₁, barX 5 X J₂⁆ = ⊥ :=
    CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ h₁.2.2.1 h₂.2.2.1 hne'
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have haX : a ∈ X := h₁.1 ha
  set a' : ↥X := ⟨a, haX⟩ with ha'
  have ha'5 : a' ^ 5 = 1 := Subtype.ext (by simpa using ha5)
  set N : Subgroup ↥X := GLAPPrimeCore 5 ↥X with hN
  have hcop : Nat.Coprime 5 (Nat.card N) :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime (G := ↥X) 5
  have hā : QuotientGroup.mk' N a' ∈ barX 5 X J₁ :=
    ⟨a', (Subgroup.mem_subgroupOf).2 ha, rfl⟩
  have hcov : barX 5 X J₂ ≤ (Subgroup.centralizer ({a'} : Set ↥X)).map (QuotientGroup.mk' N) := by
    intro jb hjb
    obtain ⟨j, rfl⟩ := QuotientGroup.mk'_surjective N jb
    have hc : QuotientGroup.mk' N a' * QuotientGroup.mk' N j =
        QuotientGroup.mk' N j * QuotientGroup.mk' N a' :=
      (Subgroup.mem_centralizer_iff.mp (hle hā) _ hjb).symm
    have hjN : j⁻¹ * a' * j * a'⁻¹ ∈ N := by
      rw [← QuotientGroup.ker_mk' N, MonoidHom.mem_ker]
      simp only [map_mul, map_inv]
      calc (QuotientGroup.mk' N j)⁻¹ * QuotientGroup.mk' N a' * QuotientGroup.mk' N j *
            (QuotientGroup.mk' N a')⁻¹
          = (QuotientGroup.mk' N j)⁻¹ * (QuotientGroup.mk' N a' * QuotientGroup.mk' N j) *
            (QuotientGroup.mk' N a')⁻¹ := by group
        _ = 1 := by rw [hc]; group
    obtain ⟨z, hzN, hz⟩ := exists_fixed_mul_normal N hcop ha'5 hjN
    have hza : a' * z = z * a' := (mul_inv_eq_iff_eq_mul.mp hz)
    refine ⟨z, ?_, ?_⟩
    · show z ∈ Subgroup.centralizer ({a'} : Set ↥X)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hza.symm
    · exact ((QuotientGroup.eq.mpr hzN).symm)
  have h60 : Nat.card ↥(barX 5 X J₂) = 60 := card_barX_eq_sixty h₂ hA₂
  have h1 : Nat.card ↥(barX 5 X J₂) ∣
      Nat.card ↥((Subgroup.centralizer ({a'} : Set ↥X)).map (QuotientGroup.mk' N)) :=
    Subgroup.card_dvd_of_le hcov
  have h2 := Subgroup.card_map_dvd (Subgroup.centralizer ({a'} : Set ↥X)) (QuotientGroup.mk' N)
  have hmap : (Subgroup.centralizer ({a'} : Set ↥X)).map X.subtype =
      X ⊓ Subgroup.centralizer ({a} : Set K) := by
    ext g
    constructor
    · rintro ⟨z, hz, rfl⟩
      refine ⟨z.2, ?_⟩
      show (z : K) ∈ Subgroup.centralizer ({a} : Set K)
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hz' : z ∈ Subgroup.centralizer ({a'} : Set ↥X) := hz
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hz')
    · rintro ⟨hgX, hg⟩
      refine ⟨⟨g, hgX⟩, ?_, rfl⟩
      show (⟨g, hgX⟩ : ↥X) ∈ Subgroup.centralizer ({a'} : Set ↥X)
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp hg)
  have h3 : Nat.card ↥(Subgroup.centralizer ({a'} : Set ↥X)) =
      Nat.card ↥(X ⊓ Subgroup.centralizer ({a} : Set K)) := by
    rw [← hmap, Subgroup.card_map_of_injective X.subtype_injective]
  rw [← h3]
  rw [h60] at h1
  exact h1.trans h2

theorem not_mem_zpowers_of_mem_component {x : K}
    (h₁ : GLAPComponent 5 (Subgroup.centralizer ({x} : Set K)) J₁)
    (hA₁ : Nonempty (↥J₁ ⧸ primeComplementCore (G := ↥J₁) 5 ≃* alternatingGroup (Fin 5)))
    {a : K} (ha : a ∈ J₁) (ha1 : a ≠ 1) (ha5 : a ^ 5 = 1) : a ∉ Subgroup.zpowers x := by
  intro hax
  obtain ⟨e⟩ := hA₁
  set N₁ : Subgroup ↥J₁ := primeComplementCore (G := ↥J₁) 5 with hN₁
  set â : ↥J₁ := ⟨a, ha⟩ with hâ
  have hcentral : ∀ w : ↥J₁, w * â = â * w := by
    intro w
    apply Subtype.ext
    have hwX : (w : K) ∈ Subgroup.centralizer ({x} : Set K) := h₁.1 w.2
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hax
    have hwc : Commute (w : K) x := (Subgroup.mem_centralizer_singleton_iff.mp hwX)
    have := (hwc.zpow_right k).eq
    rw [hk] at this
    exact this
  have hcen : (QuotientGroup.mk (s := N₁) â) ∈ Subgroup.center (↥J₁ ⧸ N₁) := by
    rw [Subgroup.mem_center_iff]
    intro q
    obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    exact congrArg _ (hcentral w)
  have hc : Subgroup.center ↥(alternatingGroup (Fin 5)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp)
  have himg : e (QuotientGroup.mk (s := N₁) â) ∈ Subgroup.center ↥(alternatingGroup (Fin 5)) := by
    rw [← Subgroup.map_center_eq e]
    exact ⟨_, hcen, rfl⟩
  rw [hc, Subgroup.mem_bot, map_eq_one_iff _ e.injective, QuotientGroup.eq_one_iff] at himg
  have hdvd : orderOf â ∣ Nat.card N₁ := Subgroup.orderOf_dvd_natCard N₁ himg
  have hord : orderOf â = 5 := by
    haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    refine orderOf_eq_prime ?_ ?_
    · exact Subtype.ext (by simpa using ha5)
    · intro h
      apply ha1
      exact congrArg Subtype.val h
  rw [hord] at hdvd
  have hcop : Nat.Coprime 5 (Nat.card N₁) :=
    CFSG.RankThreeCoreUniqueness.Helpers.primeComplementCore_coprime (G := ↥J₁) 5
  have := Nat.Coprime.eq_one_of_dvd hcop hdvd
  omega

end Comp

end CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.U44Data
