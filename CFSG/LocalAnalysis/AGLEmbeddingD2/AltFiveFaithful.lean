module

import CFSG.LocalAnalysis.AGLEmbeddingD2.AltFiveThreeRank
import CFSG.LocalAnalysis.AGLEmbeddingD2.AltOddCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.PairPhaseThree
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltDataOfAlt
public import CFSG.LocalAnalysis.AGLEmbeddingD2.AltDichotomy

public section

namespace CFSG.AGLEmbeddingD2

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers
open CFSG.AGLEmbedding

section GroupTheory

theorem exists_hom_centerQuotient {Y W : Type*} [Group Y] [Group W] (Lb : Subgroup Y)
    (β : W →* Y) (hβ : ∀ w, β w ∈ Lb ⊔ Subgroup.centralizer (Lb : Set Y)) :
    ∃ ρ : W →* ↥Lb ⧸ Subgroup.center ↥Lb,
      ∀ w, ρ w = 1 ↔ β w ∈ Subgroup.centralizer (Lb : Set Y) := by
  set C := Subgroup.centralizer (Lb : Set Y) with hC
  have hLC : Lb ≤ Subgroup.normalizer (C : Set Y) :=
    Subgroup.le_normalizer.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.centralizer_le_normalizer _)).mp
        (Subgroup.normal_subgroupOf_centralizer_normalizer _))
  have hZ : C.subgroupOf Lb = Subgroup.center ↥Lb := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_center_iff, hC, Subgroup.mem_centralizer_iff]
    constructor
    · intro hx y
      exact Subtype.ext (hx y y.2)
    · intro hx y hy
      exact congrArg Subtype.val (hx ⟨y, hy⟩)
  let _ : (C.subgroupOf Lb).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hLC
  let _ : (C.subgroupOf (Lb ⊔ C)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hLC
  let E := QuotientGroup.quotientInfEquivProdNormalizerQuotient Lb C hLC
  let E2 : (↥Lb ⧸ C.subgroupOf Lb) ≃* (↥Lb ⧸ Subgroup.center ↥Lb) :=
    QuotientGroup.quotientMulEquivOfEq hZ
  let κ : ↥(Lb ⊔ C) →* ↥Lb ⧸ Subgroup.center ↥Lb :=
    (E.symm.trans E2).toMonoidHom.comp (QuotientGroup.mk' (C.subgroupOf (Lb ⊔ C)))
  refine ⟨κ.comp (β.codRestrict (Lb ⊔ C) hβ), fun w => ?_⟩
  show κ ⟨β w, hβ w⟩ = 1 ↔ _
  rw [show κ ⟨β w, hβ w⟩ = (E.symm.trans E2)
      (QuotientGroup.mk' (C.subgroupOf (Lb ⊔ C)) ⟨β w, hβ w⟩) from rfl,
    map_eq_one_iff _ (E.symm.trans E2).injective, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]

theorem card_dvd_card_range_of_ker_le {W S Λ : Type*} [Group W] [Group S] [Group Λ] (ρ : W →* Λ)
    (ψ : W →* S) (hψ : Function.Surjective ψ) (hker : ρ.ker ≤ ψ.ker) :
    Nat.card S ∣ Nat.card ρ.range := by
  have h1 := Subgroup.index_ker ψ
  have h2 := Subgroup.index_ker ρ
  rw [MonoidHom.range_eq_top_of_surjective ψ hψ, Subgroup.card_top] at h1
  rw [← h1, ← h2]
  exact Subgroup.index_dvd_of_le hker

theorem false_of_simple_of_ker_le {W S Λ : Type*} [Group W] [Group S] [Finite S] [Nontrivial S]
    [Group Λ] [Finite Λ] [IsSimpleGroup Λ] (ρ : W →* Λ) (ψ : W →* S × S)
    (hψ : Function.Surjective ψ) (hker : ρ.ker ≤ ψ.ker)
    (hcard : Nat.card Λ ≤ Nat.card (S × S)) : False := by
  have hdvd := card_dvd_card_range_of_ker_le ρ ψ hψ hker
  have hpos : 0 < Nat.card ρ.range := Nat.card_pos
  have hle : Nat.card ρ.range ≤ Nat.card Λ := Subgroup.card_le_card_group _
  have hsurj : Function.Surjective ρ := by
    rw [← MonoidHom.range_eq_top]
    exact Subgroup.eq_top_of_card_eq _ (le_antisymm hle (hcard.trans (Nat.le_of_dvd hpos hdvd)))
  obtain ⟨s, hs⟩ := exists_ne (1 : S)
  set N₁ : Subgroup (S × S) := (⊤ : Subgroup S).prod ⊥ with hN₁
  have hN₁n : N₁.Normal := inferInstance
  set N' : Subgroup W := N₁.comap ψ with hN'
  have hN'n : N'.Normal := Subgroup.Normal.comap hN₁n ψ
  have hmapn : (N'.map ρ).Normal := Subgroup.Normal.map hN'n ρ hsurj
  rcases hmapn.eq_bot_or_eq_top with hbot | htop
  · obtain ⟨w, hw⟩ := hψ (s, 1)
    have hwN : w ∈ N' := by
      rw [hN', Subgroup.mem_comap, hw]
      exact ⟨Subgroup.mem_top s, Subgroup.one_mem _⟩
    have h1 : ρ w = 1 := by
      have : ρ w ∈ N'.map ρ := Subgroup.mem_map_of_mem ρ hwN
      rw [hbot] at this
      exact this
    have h2 : ψ w = 1 := hker h1
    rw [hw] at h2
    exact hs (congrArg Prod.fst h2)
  · obtain ⟨w, hw⟩ := hψ (1, s)
    have hmem : ρ w ∈ N'.map ρ := htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn, hnw⟩ := hmem
    have h1 : n⁻¹ * w ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnw, inv_mul_cancel]
    have h2 : ψ (n⁻¹ * w) = 1 := hker h1
    rw [map_mul, map_inv, hw, inv_mul_eq_one] at h2
    have h3 : ψ n ∈ N₁ := hn
    rw [h2] at h3
    exact hs h3.2

theorem card_dvd_or_ker_eq_top {Y Γ Γ' : Type*} [Group Y] [Group Γ] [Group Γ'] {Lb : Subgroup Y}
    (hLb : Open.IsQuasisimple ↥Lb) (f : Γ →* Y) (hf : f.range = Lb) (f' : Γ →* Γ')
    (hker : f.ker ≤ f'.ker) :
    Nat.card (↥Lb ⧸ Subgroup.center ↥Lb) ∣ Nat.card f'.range ∨ f'.ker = ⊤ := by
  let g : Γ →* Lb := f.codRestrict Lb fun γ => hf ▸ (⟨γ, rfl⟩ : f γ ∈ f.range)
  have hg : Function.Surjective g := fun y => by
    have hy : (y : Y) ∈ f.range := hf ▸ y.2
    obtain ⟨γ, hγ⟩ := hy
    exact ⟨γ, Subtype.ext hγ⟩
  have hgker : g.ker = f.ker := by
    ext γ
    simp [g, MonoidHom.mem_ker]
  have hnorm : (f'.ker.map g).Normal := Subgroup.Normal.map inferInstance g hg
  rcases ComponentClassification.Quasisimple.normal_le_center_or_eq_top hLb (f'.ker.map g) with
    hc | htop
  · left
    let g' : Γ →* ↥Lb ⧸ Subgroup.center ↥Lb := (QuotientGroup.mk' (Subgroup.center ↥Lb)).comp g
    have hg' : Function.Surjective g' := (QuotientGroup.mk'_surjective _).comp hg
    have hle : f'.ker ≤ g'.ker := fun γ hγ => by
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff]
      exact hc (Subgroup.mem_map_of_mem g hγ)
    have h1 := Subgroup.index_ker g'
    have h2 := Subgroup.index_ker f'
    rw [MonoidHom.range_eq_top_of_surjective g' hg', Subgroup.card_top] at h1
    rw [← h1, ← h2]
    exact Subgroup.index_dvd_of_le hle
  · right
    rw [eq_top_iff]
    intro γ _
    have hmem : g γ ∈ f'.ker.map g := htop ▸ Subgroup.mem_top _
    obtain ⟨k, hk, hkγ⟩ := hmem
    have h1 : k⁻¹ * γ ∈ g.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkγ, inv_mul_cancel]
    have h2 : k⁻¹ * γ ∈ f'.ker := hker (hgker ▸ h1)
    simpa using f'.ker.mul_mem hk h2

end GroupTheory

section Bar

theorem range_barElt {G : Type} [Group G] {M W : Subgroup G} (hWM : W ≤ M) :
    (barElt M hWM).range = barM M W := by
  rw [barElt, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

end Bar

namespace D2AltModel

theorem card_B {X : Type} [Group X] {p : ℕ} {A X₀ K : Subgroup X}
    {e : K ≃* alternatingGroup (Fin (2 * p))} (M : D2AltModel p A X₀ K e) :
    Nat.card M.B = Nat.card (alternatingGroup (Fin p) × alternatingGroup (Fin p)) := by
  rw [← Subgroup.card_map_of_injective M.injective, M.map_B]
  exact (Nat.card_congr (AltData.altPairEquiv M.card₁ M.card₂ M.disjoint).toEquiv).symm

end D2AltModel

namespace D2AltData

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {M H R X : Subgroup G}

theorem psi_eq_one_of_faithful (h : D2AltData p M H R X) {c₀ c₁ s : G} {g : ℕ} {W : Subgroup G}
    {ψ : W →* alternatingGroup (Fin p) × alternatingGroup (Fin p)}
    (hsc : AltScalar p (H ⊓ M) X c₀ c₁ s g) (hWM : W ≤ M) (hXW : X ≤ W)
    (hsurj : Function.Surjective ψ) (hker : ψ.ker = (GLBPrimeCore p H).subgroupOf W)
    (hc₀ : ∀ w : W, (w : G) = c₀ → (ψ w).2 = 1) (hc₁ : ∀ w : W, (w : G) = c₁ → (ψ w).1 = 1)
    {Lb : Subgroup (↥M ⧸ CFSG.pCore 2 ↥M)}
    (hnormL : barM M W ≤ Subgroup.normalizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)))
    (hfaith : barM M X ⊓ Subgroup.centralizer (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥) :
    ∀ w ∈ centralizerBar M hWM Lb, ψ w = 1 := by
  have hp : p.Prime := Fact.out
  have hp5 := h.five_le
  have hX : IsElemAbelian p X := h.elem
  have hc₀X : c₀ ∈ X := hsc.mem_zero
  have hc₁X : c₁ ∈ X := hsc.mem_one
  have : IsSimpleGroup (alternatingGroup (Fin p)) :=
    alternatingGroup.isSimpleGroup (by simpa using hp5)
  have hZ : Subgroup.center (alternatingGroup (Fin p)) = ⊥ :=
    alternatingGroup.center_eq_bot (by simp; omega)
  set w₀ : W := ⟨c₀, hXW hc₀X⟩ with hw₀
  set w₁ : W := ⟨c₁, hXW hc₁X⟩ with hw₁
  have hw₀p : w₀ ^ p = 1 := Subtype.ext (hX.2 c₀ hc₀X)
  have hw₁p : w₁ ^ p = 1 := Subtype.ext (hX.2 c₁ hc₁X)
  have hc₀ne : c₀ ≠ 1 := by
    intro hc
    have hc' : c₁ = 1 := by rw [← hsc.conj_zero, hc]; group
    have hXbot : X = ⊥ := by rw [hsc.span, hc, hc']; simp
    have := h.card
    rw [hXbot, Subgroup.card_bot] at this
    have h2 : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp.one_lt
    omega
  have hc₁ne : c₁ ≠ 1 := by
    intro hc
    refine hc₀ne ?_
    have h1 : s * c₀ * s⁻¹ = 1 := by rw [hsc.conj_zero, hc]
    simpa using h1
  have hnotC : ∀ w : W, (w : G) ∈ X → w ≠ 1 → w ∉ centralizerBar M hWM Lb := by
    intro w hwX hw1 hwC
    have hmem : barElt M hWM w ∈ barM M X ⊓ Subgroup.centralizer
        (Lb : Set (↥M ⧸ CFSG.pCore 2 ↥M)) :=
      ⟨Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hwX), hwC⟩
    rw [hfaith, Subgroup.mem_bot] at hmem
    exact hw1 (Subtype.ext (h.pair.eq_one_of_mem_twoCore hX hwX
      (coe_mem_pCoreOf_two_of_mk_eq_one _ hmem)))
  have hker' : ∀ n : W, ψ n = 1 → (orderOf n).Coprime p := by
    intro n hn
    have hnN : (n : G) ∈ GLBPrimeCore p H := by
      have hn' : n ∈ ψ.ker := hn
      rw [hker] at hn'
      exact hn'
    have hdvd : orderOf n ∣ Nat.card (GLBPrimeCore p H) := by
      rw [← Subgroup.orderOf_coe]
      exact Subgroup.orderOf_dvd_natCard _ hnN
    exact Nat.Coprime.coprime_dvd_left hdvd (glbPrimeCore_coprime p H).symm
  have := normal_centralizerBar hWM hnormL
  have hnormψ : ((centralizerBar M hWM Lb).map ψ).Normal :=
    Subgroup.Normal.map inferInstance ψ hsurj
  have hpsi : ∀ x : W, x ^ p = 1 → ψ x ∈ (centralizerBar M hWM Lb).map ψ →
      x ∈ centralizerBar M hWM Lb := fun x hxp hx =>
    mem_centralizerBar_of_psi_mem hWM hnormL hker' hxp hx
  intro w hw
  refine Prod.ext ?_ ?_
  · refine fst_eq_one_of_normal hZ (a := (ψ w₀).1) (fun hmem => hnotC w₀ hc₀X
      (fun h1 => hc₀ne (congrArg Subtype.val h1)) (hpsi w₀ hw₀p ?_))
      (Subgroup.mem_map_of_mem ψ hw)
    rwa [show ψ w₀ = ((ψ w₀).1, 1) from Prod.ext rfl (hc₀ w₀ rfl)]
  · refine snd_eq_one_of_normal hZ (b := (ψ w₁).2) (fun hmem => hnotC w₁ hc₁X
      (fun h1 => hc₁ne (congrArg Subtype.val h1)) (hpsi w₁ hw₁p ?_))
      (Subgroup.mem_map_of_mem ψ hw)
    rwa [show ψ w₁ = (1, (ψ w₁).2) from Prod.ext (hc₁ w₁ rfl) rfl]

end D2AltData

section AltTen

variable {G : Type} [Group G] [Finite G] {p : ℕ} {P : Sylow p G} {M A H : Subgroup G}
  {Rbar : Sylow p (H ⧸ primeComplementCore (G := H) p)}
  {K : Subgroup (H ⧸ primeComplementCore (G := H) p)}

theorem D2Escape.false_of_faithful_component_alt [Fact p.Prime] (h : D2Escape p P M A H A)
    (hglob : AGLGlobal G) (hD1 : D1For G) (hα : KFactThreeOrFiveDvd)
    (hSch : KFactCatalogSchreier)
    (hB3 : ∀ L : Subgroup G, IsWeakSBlock M (pCoreOf 2 H) L → BlockHasThree M (pCoreOf 2 H) L)
    (hRbar : (Rbar : Subgroup _) = (A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
    (hK : D2AlmostSimple p (H ⧸ primeComplementCore (G := H) p) Rbar
      ((A.subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p)))
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (primeComplementCore p))) K)
    (e : K ≃* alternatingGroup (Fin (2 * p))) (hp5 : 5 ≤ p)
    {L : Subgroup G} (hL : IsTwoPrimeComponent M L) (hLK : L ≤ H ⊓ M)
    (hfaith : barM M A ⊓ Subgroup.centralizer (barM M L : Set (↥M ⧸ CFSG.pCore 2 ↥M)) = ⊥) :
    False := by
  have hp : p.Prime := Fact.out
  have hdata : D2AltData p M H A A := h.altData_of_alt hglob hRbar hK e hp5
  obtain ⟨c₀, c₁, s, g, W, ψ, hsc, hWK, hW, hXW, -, hsurj, hker, hc₀, hc₁, -⟩ := hdata.perfect
  have hWM : W ≤ M := hWK.trans inf_le_right
  have hLb : IsComponentOf (barM M L) ⊤ := hL.component
  have hnorm := hdata.pair.le_normalizer_component hD1 hα hB3 hWK hW hLb
  have hsup := hdata.pair.le_sup_centralizer_component hD1 hα hSch hB3 hWK hW hLb
  have hpsi := hdata.psi_eq_one_of_faithful hsc hWM hXW hsurj hker hc₀ hc₁ hnorm hfaith
  obtain ⟨ρ, hρ⟩ := exists_hom_centerQuotient (barM M L) (barElt M hWM)
    (fun w => hsup (barElt_mem_barM hWM w))
  have hρker : ρ.ker ≤ ψ.ker := fun w hw => hpsi w ((hρ w).mp hw)
  have hLsimple : IsSimpleGroup (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) := hLb.2.2.2
  have hSsimple : IsSimpleGroup (alternatingGroup (Fin p)) :=
    alternatingGroup.isSimpleGroup (by simpa using hp5)
  have hLH : L ≤ H := hLK.trans inf_le_left
  have hLM : L ≤ M := hLK.trans inf_le_right
  let f : ↥L →* ↥M ⧸ CFSG.pCore 2 ↥M := barElt M hLM
  let f' : ↥L →* H ⧸ primeComplementCore (G := H) p :=
    (QuotientGroup.mk' (primeComplementCore (G := H) p)).comp (Subgroup.inclusion hLH)
  have hf : f.range = barM M L := range_barElt hLM
  have hff' : f.ker ≤ f'.ker := by
    intro ℓ hℓ
    have h1 : (ℓ : G) ∈ pCoreOf 2 M := coe_mem_pCoreOf_two_of_mk_eq_one _ hℓ
    exact (mem_glbPrimeCore_iff_mk_eq_one (⟨ℓ, hLH ℓ.2⟩ : H)).mp
      (hdata.pair.twoCore_M_le_glbPrimeCore h1)
  rcases card_dvd_or_ker_eq_top hLb.2.2 f hf f' hff' with hdvd | htop
  ·
    obtain ⟨Mo⟩ := hK.nonempty_altModel hp5 e
    have hJX : f'.range ≤ ((H ⊓ M).subgroupOf H).map
        (QuotientGroup.mk' (primeComplementCore (G := H) p)) := by
      rintro _ ⟨ℓ, rfl⟩
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (hLK ℓ.2))
    have hperf : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL.perfect
    have hperf' : Group.IsPerfect f'.range := Group.IsPerfect.range f'
    have hle := Mo.le_B_of_perfect hJX (Subgroup.isPerfect_iff.mp hperf')
    have hcard : Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∣
        Nat.card (alternatingGroup (Fin p) × alternatingGroup (Fin p)) :=
      hdvd.trans ((Subgroup.card_dvd_of_le hle).trans (dvd_of_eq Mo.card_B))
    exact false_of_simple_of_ker_le ρ ψ hsurj hρker (Nat.le_of_dvd Nat.card_pos hcard)
  ·
    have hLle : L ≤ GLBPrimeCore p H := fun x hx =>
      (mem_glbPrimeCore_iff_mk_eq_one (⟨x, hLH hx⟩ : H)).mpr
        (MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥L) : (⟨x, hx⟩ : ↥L) ∈ f'.ker))
    have hpS : p ∣ Nat.card (alternatingGroup (Fin p) × alternatingGroup (Fin p)) := by
      rw [Nat.card_prod]
      have : Nontrivial (Fin p) := Fin.nontrivial_iff_two_le.mpr (by omega)
      have hcard := two_mul_nat_card_alternatingGroup (α := Fin p)
      rw [Nat.card_perm, show Nat.card (Fin p) = p by simp] at hcard
      have hpf : p ∣ Nat.factorial p := Nat.dvd_factorial hp.pos le_rfl
      rw [← hcard] at hpf
      have hcop : Nat.Coprime p 2 := (Nat.coprime_primes hp Nat.prime_two).mpr (by omega)
      exact Dvd.dvd.mul_right ((Nat.Coprime.dvd_mul_left hcop).mp hpf) _
    have h1 := card_dvd_card_range_of_ker_le ρ ψ hsurj hρker
    have h2 : Nat.card ρ.range ∣ Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) :=
      Subgroup.card_subgroup_dvd_card _
    have h3 : Nat.card (↥(barM M L) ⧸ Subgroup.center ↥(barM M L)) ∣ Nat.card ↥(barM M L) :=
      Subgroup.index_dvd_card _
    have h4 : Nat.card ↥(barM M L) ∣ Nat.card ↥L := by
      have := Subgroup.card_range_dvd f
      rwa [hf] at this
    have h5 : Nat.card ↥L ∣ Nat.card (GLBPrimeCore p H) := Subgroup.card_dvd_of_le hLle
    have h6 := hpS.trans (h1.trans (h2.trans (h3.trans (h4.trans h5))))
    exact hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (glbPrimeCore_coprime p H) h6)

end AltTen

end CFSG.AGLEmbeddingD2
