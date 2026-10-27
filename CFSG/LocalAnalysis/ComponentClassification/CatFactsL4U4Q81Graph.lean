module

public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81Conj
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsL4U4Q81E8
public import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofQ81P2

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X}

namespace Standing

theorem not_conj_t_of_isOfType (h : Standing t L 3 4) {β : X}
    {J : Subgroup ↥(centralizer ({β} : Set X))}
    (htype : IsOfType (fun (Y : Type) [Group Y] =>
      Blueprint.LieModel Y .PSL 4 3 1 ∨ Blueprint.LieModel Y .PSU 4 3 1) ↥J) (c : X) :
    c * t * c⁻¹ ≠ β := by
  intro hc
  obtain ⟨⟨hJp, -⟩, Y, _, hY, ⟨eY⟩⟩ := htype
  have hY128 : 128 ∣ Nat.card Y := by
    rcases hY with hY | hY
    · rw [GH74.card_of_lieModel_PSL four_ne_zero hY]
      decide
    · rw [GH74.card_of_lieModel_PSU four_ne_zero (by norm_num) hY]
      decide
  have hJ128 : 128 ∣ Nat.card J := by
    have h1 : Nat.card Y = Nat.card (↥J ⧸ Open.fusionZStar ↥J) := Nat.card_congr eY.symm.toEquiv
    exact hY128.trans (h1 ▸ Subgroup.card_quotient_dvd_card _)
  set JX : Subgroup X := (J.map (centralizer ({β} : Set X)).subtype).map
      (MulAut.conj c⁻¹).toMonoidHom with hJX
  have hCt : (centralizer ({β} : Set X)).map (MulAut.conj c⁻¹).toMonoidHom =
      centralizer {t} := by
    rw [L415.map_conj_centralizer, ← hc]
    congr 2
    group
  have hJXt : JX ≤ centralizer {t} := by
    rw [← hCt]
    exact map_mono (map_subtype_le J)
  have hJXp : Group.IsPerfect ↥JX := by
    have h1 : Group.IsPerfect ↥(J.map (centralizer ({β} : Set X)).subtype) :=
      Group.IsPerfect.ofSurjective (f := (J.equivMapOfInjective _
        (subtype_injective _)).toMonoidHom) (MulEquiv.surjective _)
    exact Group.IsPerfect.ofSurjective (f := ((J.map (centralizer
      ({β} : Set X)).subtype).equivMapOfInjective _ (MulAut.conj c⁻¹).injective).toMonoidHom)
        (MulEquiv.surjective _)
  have hJL : JX ≤ L := by
    have h1 := le_perfectResidual_map hJXt hJXp
    rwa [h.dihedral.residual] at h1
  have hcard : Nat.card JX = Nat.card J := by
    rw [hJX, card_map_of_injective (MulAut.conj c⁻¹).injective,
      card_map_of_injective (subtype_injective _)]
  have hL128 : 128 ∣ Nat.card L := (hcard ▸ hJ128).trans (card_dvd_of_le hJL)
  have hLbar : Nat.card (Bar L) = 265680 := by
    rw [GH74.card_of_lieModel_PSL two_ne_zero h.config.lieModel]
    rfl
  have hLeq : Nat.card L = Nat.card (Bar L) * Nat.card (pPrimeCore 2 ↥L) :=
    card_eq_card_quotient_mul_card_subgroup _
  have hcop : Nat.Coprime 128 (Nat.card (pPrimeCore 2 ↥L)) := by
    have h1 := Nat.Coprime.pow_left 7 (pPrimeCore_coprime_card (p := 2) (G := ↥L))
    norm_num at h1
    exact h1
  have h2 : 128 ∣ 265680 := by
    rw [← hLbar]
    exact hcop.dvd_of_dvd_mul_right (hLeq ▸ hL128)
  norm_num at h2

end Standing

namespace Setting46e

variable {S : Subgroup X} {w z : X} {V : Subgroup X} {i₀ j₀ : ℕ}

theorem mk_conj_t_not_mem (hs : Setting46e t L 3 4 S w z V i₀ j₀)
    (hQ : ∀ i j : ℕ, IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) →
      (Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSL 4 3 1 ∨
        Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) ⧸
          center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))) .PSU 4 3 1) →
      hs.setup.Q81Data i j)
    {i j : ℕ} (hD : hs.setup.Q81Data i j)
    (hβt : ∀ c : X, c * t * c⁻¹ ≠ w ^ (orderOf w / 2) * t ^ i * z ^ j) {g : X}
    (hg : g * t * g⁻¹ ∈ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))
    {I : Subgroup (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))}
    (hI : Q81.IsInnDiag (layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))) I) :
    (QuotientGroup.mk ⟨g * t * g⁻¹, hg⟩ : MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)) ∉ I := by
  intro hτI
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have ht2 : t * t = 1 := by rw [← sq, ← hs.standing.config.orderOf_eq, pow_orderOf_eq_one]
  have hτ2 : g * t * g⁻¹ * (g * t * g⁻¹) = 1 := by
    rw [show g * t * g⁻¹ * (g * t * g⁻¹) = g * (t * t) * g⁻¹ by group, ht2]
    group
  have hτ'2 : (⟨g * t * g⁻¹, hg⟩ : ↥(centralizer
      ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X))) * ⟨g * t * g⁻¹, hg⟩ = 1 :=
    Subtype.ext hτ2
  have hodd : Odd (Nat.card (pPrimeCore 2 ↥(centralizer
      ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))) :=
    Nat.coprime_two_left.mp pPrimeCore_coprime_card
  have hπC := map_centralizer_eq hodd hτ'2
  have hMC := map_subtype_centralizer hg
  have hnc : ¬ IsPGroup 2 (↥(centralizer ({g * t * g⁻¹} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}) ⧸ pPrimeCore 2 ↥(centralizer
        ({g * t * g⁻¹} : Set X) ⊓ centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})) := by
    intro hP
    let e₁ := ((centralizer ({(⟨g * t * g⁻¹, hg⟩ : ↥(centralizer
      ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))} : Set _)).equivMapOfInjective _
        (subtype_injective _)).trans (MulEquiv.subgroupCongr hMC)
    let f := (MulEquiv.subgroupCongr hπC).toMonoidHom.comp
      (((QuotientGroup.mk' _).subgroupMap _).comp e₁.symm.toMonoidHom)
    have hf : Function.Surjective f := by
      intro y
      obtain ⟨y₁, rfl⟩ := (MulEquiv.subgroupCongr hπC).surjective y
      obtain ⟨y₂, rfl⟩ := (QuotientGroup.mk' _).subgroupMap_surjective _ y₁
      refine ⟨e₁ y₂, ?_⟩
      change (MulEquiv.subgroupCongr hπC) (((QuotientGroup.mk' _).subgroupMap _)
        (e₁.symm (e₁ y₂))) = _
      rw [MulEquiv.symm_apply_apply]
    refine hD.not_isPGroup_centralizer' ?_ (Q81.isPGroup_quotient_of_surjective f hf hP)
    rw [← map_mul, hτ'2, map_one]
  have hgβ : g * t * g⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) =
      (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (g * t * g⁻¹) := mem_centralizer_singleton_iff.mp hg
  have hβ'H : g⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g ∈ centralizer ({t} : Set X) := by
    rw [mem_centralizer_singleton_iff]
    calc g⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g * t =
          g⁻¹ * ((w ^ (orderOf w / 2) * t ^ i * z ^ j) * (g * t * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * t * g⁻¹) * (w ^ (orderOf w / 2) * t ^ i * z ^ j)) * g := by rw [hgβ]
      _ = t * (g⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g) := by group
  have hβ'2 : orderOf (g⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g) = 2 := by
    have h1 := (MulAut.conj g⁻¹).orderOf_eq (w ^ (orderOf w / 2) * t ^ i * z ^ j)
    rw [MulAut.conj_apply, inv_inv, hs.setup.orderOf_beta i j] at h1
    exact h1
  have hZp : IsPGroup 2 (zpowers (g⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hβ'2, pow_one])
  obtain ⟨P, hP, hPle⟩ := Q81.exists_isSylowOf_ge hZp (zpowers_le.mpr hβ'H)
  obtain ⟨k, hk, hkP⟩ := L415.exists_map_conj hs.sylow hP
  have hβ'P := hPle (mem_zpowers (g⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g))
  rw [hkP] at hβ'P
  obtain ⟨s, hsS, hse⟩ := hβ'P
  have hse' : k * s * k⁻¹ = g⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g := hse
  have hkt : k * t = t * k := mem_centralizer_singleton_iff.mp hk
  have hdτ : (k⁻¹ * g⁻¹) * (g * t * g⁻¹) * (k⁻¹ * g⁻¹)⁻¹ = t := by
    calc (k⁻¹ * g⁻¹) * (g * t * g⁻¹) * (k⁻¹ * g⁻¹)⁻¹ = k⁻¹ * (t * k) := by group
      _ = t := by rw [← hkt]; group
  have hdβ : (k⁻¹ * g⁻¹) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (k⁻¹ * g⁻¹)⁻¹ = s := by
    calc (k⁻¹ * g⁻¹) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (k⁻¹ * g⁻¹)⁻¹ =
          k⁻¹ * (g⁻¹ * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * g) * k := by group
      _ = s := by rw [← hse']; group
  have hs2 : s ^ 2 = 1 := by
    have h1 : orderOf s = 2 := by
      rw [← hdβ, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hs.setup.orderOf_beta i j]
    rw [← h1, pow_orderOf_eq_one]
  have hs1 : s ≠ 1 := by
    intro h1
    have h2 : orderOf s = 2 := by
      rw [← hdβ, ← MulAut.conj_apply, MulEquiv.orderOf_eq, hs.setup.orderOf_beta i j]
    rw [h1, orderOf_one] at h2
    exact absurd h2 (by decide)
  have hst : s ≠ t := by
    intro h1
    apply hβt (k⁻¹ * g⁻¹)⁻¹
    have h2 : (k⁻¹ * g⁻¹) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (k⁻¹ * g⁻¹)⁻¹ = t :=
      hdβ.trans h1
    calc (k⁻¹ * g⁻¹)⁻¹ * t * (k⁻¹ * g⁻¹)⁻¹⁻¹ = (k⁻¹ * g⁻¹)⁻¹ * ((k⁻¹ * g⁻¹) *
          (w ^ (orderOf w / 2) * t ^ i * z ^ j) * (k⁻¹ * g⁻¹)⁻¹) * (k⁻¹ * g⁻¹) := by
          rw [h2, inv_inv]
      _ = w ^ (orderOf w / 2) * t ^ i * z ^ j := by group
  have hncs : ¬ IsPGroup 2 (↥(centralizer ({t} : Set X) ⊓ centralizer {s}) ⧸
      pPrimeCore 2 ↥(centralizer ({t} : Set X) ⊓ centralizer {s})) := by
    intro hP'
    apply hnc
    have hmap : (centralizer ({g * t * g⁻¹} : Set X) ⊓
        centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j}).map
          (MulAut.conj (k⁻¹ * g⁻¹)).toMonoidHom = centralizer ({t} : Set X) ⊓ centralizer {s} := by
      rw [map_inf_eq _ _ _ (MulAut.conj (k⁻¹ * g⁻¹)).injective, L415.map_conj_centralizer,
        L415.map_conj_centralizer, hdτ, hdβ]
    let e₂ := ((((centralizer ({g * t * g⁻¹} : Set X) ⊓
      centralizer {w ^ (orderOf w / 2) * t ^ i * z ^ j})).equivMapOfInjective _
        (MulAut.conj (k⁻¹ * g⁻¹)).injective).trans (MulEquiv.subgroupCongr hmap)).symm
    exact Q81.isPGroup_quotient_of_surjective e₂.toMonoidHom e₂.surjective hP'
  obtain ⟨g', hg'H, i'', j'', hg's, -⟩ := hs.lemma44b s hsS hs2 hs1 hst hncs
  have hg't : g' * t * g'⁻¹ = t := by
    rw [mem_centralizer_singleton_iff.mp hg'H]
    group
  have hcβ : (g' * (k⁻¹ * g⁻¹)) * (w ^ (orderOf w / 2) * t ^ i * z ^ j) *
      (g' * (k⁻¹ * g⁻¹))⁻¹ = w ^ (orderOf w / 2) * t ^ i'' * z ^ j'' := by
    rw [← hg's, ← hdβ]
    group
  have hcτ : (g' * (k⁻¹ * g⁻¹)) * (g * t * g⁻¹) * (g' * (k⁻¹ * g⁻¹))⁻¹ = t := by
    calc (g' * (k⁻¹ * g⁻¹)) * (g * t * g⁻¹) * (g' * (k⁻¹ * g⁻¹))⁻¹ =
          g' * ((k⁻¹ * g⁻¹) * (g * t * g⁻¹) * (k⁻¹ * g⁻¹)⁻¹) * g'⁻¹ := by group
      _ = t := by rw [hdτ, hg't]
  set Ψ := Q81.mbarConj (g' * (k⁻¹ * g⁻¹)) hcβ with hΨ
  have hΨτ : Ψ (QuotientGroup.mk ⟨g * t * g⁻¹, hg⟩) = hs.setup.tBar i'' j'' := by
    rw [hΨ, Q81.mbarConj_mk _ hcβ hg
      (by rw [hcτ]; exact hs.setup.t_mem_centralizer_beta i'' j'')]
    exact congrArg QuotientGroup.mk (Subtype.ext hcτ)
  have hΨE := Q81.map_layer_equiv Ψ
  let eE := ((layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j))).equivMapOfInjective _
    Ψ.injective).trans (MulEquiv.subgroupCongr hΨE)
  have hE'' : IsQuasisimple ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i'' * z ^ j''))) :=
    LocalCores.isQuasisimple_of_mulEquiv eE hD.quasisimple
  let eZ := QuotientGroup.congr _ _ eE (Q81.map_center_equiv eE)
  have hm'' : Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i'' * z ^ j''))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i'' * z ^ j'')))) .PSL 4 3 1 ∨
      Blueprint.LieModel (↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i'' * z ^ j''))) ⧸
        center ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i'' * z ^ j'')))) .PSU 4 3 1 := by
    rcases hD.card_center_dvd.2 with hL | hU
    · exact .inl (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eZ hL)
    · exact .inr (CFSG.LieType.CurtisTits.lieModel_of_mulEquiv eZ hU)
  have hD'' := hQ i'' j'' hE'' hm''
  have hI'' := hI.map Ψ
  rw [hΨE] at hI''
  exact hD''.graph _ hI'' (hΨτ ▸ mem_map_of_mem Ψ.toMonoidHom hτI)

end Setting46e

end CFSG.ComponentClassification.HarrisLit
