module

public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cLayer
public import CFSG.GH74.GLS.IVK.Lifted.PGLQuot
public import CFSG.GH74.GLS.C3.Layer1.Thm1P31cEnv

public section

open Subgroup CFSG CFSG.ABGLocalTools CFSG.ComponentClassification CFSG.GH74.GLS CFSG.GH74.GLS.IVK
  CFSG.GH74.GLS.TwoThin CFSG.GH74.GLS.C3.Layer1 CFSG.GH74.GLS.C3.Layer1.Thm1 CFSG.GH74.GLS.C3.Layer1.Thm1P31c

namespace CFSG.GH74.GLS.C3.Layer1.Thm1L32

theorem exists_unique_twoComponent {A Y₁ : Type} [Group A] [Finite A] [Group Y₁] (ρ : A →* Y₁)
    (hρ : Function.Surjective ρ) (hodd : Odd (Nat.card ρ.ker))
    (S : Subgroup Y₁) [S.Normal] (hS : IsSimpleGroup ↥S) (hSna : ∃ a b : ↥S, a * b ≠ b * a)
    (hperf : ∀ J : Subgroup Y₁, J ≠ ⊥ → ⁅J, J⁆ = J → J.IsSubnormal → J = S) :
    ∃ L : Subgroup A, TwoComponents.IsTwoComponent L ∧ L.map ρ = S ∧
      Nonempty ((↥L ⧸ pPrimeCore 2 ↥L) ≃* ↥S) ∧
      ∀ L' : Subgroup A, TwoComponents.IsTwoComponent L' → L' = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Y₁ := Finite.of_surjective ρ hρ
  have himg : ∀ L' : Subgroup A, TwoComponents.IsTwoComponent L' → L'.map ρ = S := by
    intro L' hL'
    apply hperf
    · intro hbot
      have hle : L' ≤ ρ.ker := (Subgroup.map_eq_bot_iff _).1 hbot
      have hoddL : Odd (Nat.card ↥L') := Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)
      have hsolv : Group.IsSolvable ↥L' := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddL
      have hne : Nontrivial ↥L' := TwoComponents.nontrivial hL'
      have h1 := Group.IsSolvable.commutator_lt_top_of_nontrivial ↥L'
      have : Group.IsPerfect ↥L' := Group.isPerfect_def.mpr (TwoComponents.perfect hL')
      rw [this.commutator_eq_top] at h1
      exact lt_irrefl _ h1
    · rw [← Subgroup.map_commutator, commutator_self_of_isTwoComponent' hL']
    · exact (Components.mathlib_subnormal_of_chain hL'.1 Subgroup.IsSubnormal.top).map hρ
  obtain ⟨L, hL, -, -, hquo⟩ := exists_twoComponent_of_surj ρ hρ hodd S hS hSna
  refine ⟨L, hL, himg L hL, hquo, fun L' hL' => ?_⟩
  have h1 : L' ≤ L := TwoComponentSubnormal.le_of_odd_kernel_map_le ρ hρ hodd L' L hL' hL.1
    (by rw [himg L' hL', himg L hL])
  have h2 : L ≤ L' := TwoComponentSubnormal.le_of_odd_kernel_map_le ρ hρ hodd L L' hL hL'.1
    (by rw [himg L' hL', himg L hL])
  exact le_antisymm h1 h2


variable {G : Type} [Group G] [Finite G]

theorem layer_data {x f : G} {K : Subgroup G}
    (hKC : K ≤ centralizer ({x} : Set G))
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hfC : f ∈ centralizer ({x} : Set G)) (hf2 : orderOf f = 2)
    {Ω : Type} [Group Ω]
    (e : ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)) ≃* Ω)
    (S : Subgroup Ω) [S.Normal] (hS : IsSimpleGroup ↥S) (hSna : ∃ a b : ↥S, a * b ≠ b * a)
    (hperf : ∀ J : Subgroup Ω, J ≠ ⊥ → ⁅J, J⁆ = J → J.IsSubnormal → J = S) :
    ∃ Λ : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G)) Λ ∧
      Λ ≤ K ∧ pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) = Λ ∧
      Nonempty (kBar Λ ≃* ↥S) ∧ Subgroup.center (kBar Λ) = ⊥ ∧
      ((Λ.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) =
        (S.map e.symm.toMonoidHom).map (fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)).subtype) ∧
      (∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G), ∀ a ∈ Λ, c * a * c⁻¹ ∈ Λ) ∧
      pPrimeCoreOf 2 Λ ≤ pPrimeCoreOf 2 K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite Ω := Finite.of_equiv _ e.toEquiv
  set H₀ : Subgroup G := K ⊓ centralizer ({f} : Set G) with hH₀
  let ρ : ↥H₀ →* Ω := e.toMonoidHom.comp (centMap hKN hfC)
  have hρ : Function.Surjective ρ := e.surjective.comp (centMap_surjective hKN hfC hf2)
  have hker : ρ.ker = (centMap hKN hfC).ker := by
    ext h
    simp only [MonoidHom.mem_ker, ρ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
    exact ⟨fun h1 => e.injective (by rw [h1, map_one]), fun h1 => by rw [h1, map_one]⟩
  have hkodd : Odd (Nat.card ρ.ker) := hker ▸ centMap_ker_odd hKN hfC
  obtain ⟨L₀, hL₀, hL₀map, ⟨eL⟩, huniq⟩ := exists_unique_twoComponent ρ hρ hkodd S hS hSna hperf
  set W : Subgroup G := centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G) with hW
  have hH₀W : H₀ ≤ W := fun h hh => ⟨hKC hh.1, hh.2⟩
  have hΛH₀ : L₀.map H₀.subtype ≤ H₀ := Subgroup.map_subtype_le L₀
  have hΛ2 : TwoComponents.IsTwoComponent ((L₀.map H₀.subtype).subgroupOf H₀) := by
    have : (L₀.map H₀.subtype).subgroupOf H₀ = L₀ :=
      Subgroup.comap_map_eq_self_of_injective H₀.subtype_injective L₀
    rw [this]
    exact hL₀
  have hnorm : (H₀.subgroupOf W).Normal := ⟨fun n hn g => by
    have hn' : (n : G) ∈ H₀ := hn
    refine Subgroup.mem_subgroupOf.2 ⟨hKN (g : G) g.2.1 (n : G) hn'.1, ?_⟩
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ g.2.2 hn'.2) (Subgroup.inv_mem _ g.2.2)⟩
  have hΛW := TwoComponentTransport.extend_nested (L₀.map H₀.subtype) H₀ W hΛH₀ hH₀W
    (Subgroup.Normal.isSubnormal hnorm) hΛ2
  let ρL : ↥L₀ →* ↥S := (ρ.comp L₀.subtype).codRestrict S (fun l => by
    rw [← hL₀map]
    exact Subgroup.mem_map_of_mem _ l.2)
  have hρL : Function.Surjective ρL := by
    intro s
    have hs : (s : Ω) ∈ L₀.map ρ := by rw [hL₀map]; exact s.2
    obtain ⟨l, hl, hls⟩ := hs
    exact ⟨⟨l, hl⟩, Subtype.ext hls⟩
  have hkoddL : Odd (Nat.card ρL.ker) := by
    let ι : ↥ρL.ker →* ↥ρ.ker :=
      ((L₀.subtype.comp ρL.ker.subtype).codRestrict ρ.ker (fun m => by
        have h := MonoidHom.mem_ker.1 m.2
        exact MonoidHom.mem_ker.2 (congrArg Subtype.val h)))
    have hι : Function.Injective ι := by
      intro a b hab
      have h1 : (ι a).val = (ι b).val := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext h1)
    exact Odd.of_dvd_nat hkodd (Subgroup.card_dvd_of_injective ι hι)
  have hcoreL₀ : pPrimeCore 2 ↥L₀ = ρL.ker :=
    pPrimeCore_eq_ker_of_odd ρL hρL hkoddL (pPrimeCore_eq_bot_of_simple hS hSna)
  let eΛ₀ : ↥L₀ ≃* ↥(L₀.map H₀.subtype) :=
    Subgroup.equivMapOfInjective L₀ H₀.subtype H₀.subtype_injective
  refine ⟨L₀.map H₀.subtype, TwoThin.isPCompIn_two_iff.2 ⟨hΛH₀.trans hH₀W, hΛW⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨l, -, rfl⟩ := hg
    exact l.2.1
  ·
    have hset : {L | IsPCompIn 2 H₀ L} = {L₀.map H₀.subtype} := by
      ext L
      simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
      constructor
      · intro hL
        obtain ⟨hLH, hL2⟩ := TwoThin.isPCompIn_two_iff.1 hL
        have h1 := huniq _ hL2
        rw [← Subgroup.map_subgroupOf_eq_of_le hLH, h1]
      · rintro rfl
        exact TwoThin.isPCompIn_two_iff.2 ⟨hΛH₀, hΛ2⟩
    unfold pLayerOf
    rw [hset, sSup_singleton]
  · let eΛ : ↥L₀ ≃* ↥(L₀.map H₀.subtype) :=
      Subgroup.equivMapOfInjective L₀ H₀.subtype H₀.subtype_injective
    let eq1 : (↥L₀ ⧸ pPrimeCore 2 ↥L₀) ≃* kBar (L₀.map H₀.subtype) :=
      QuotientGroup.congr _ _ eΛ (pPrimeCore_map_iso 2 eΛ)
    exact ⟨eq1.symm.trans eL⟩
  · let eΛ : ↥L₀ ≃* ↥(L₀.map H₀.subtype) :=
      Subgroup.equivMapOfInjective L₀ H₀.subtype H₀.subtype_injective
    let eq1 : (↥L₀ ⧸ pPrimeCore 2 ↥L₀) ≃* kBar (L₀.map H₀.subtype) :=
      QuotientGroup.congr _ _ eΛ (pPrimeCore_map_iso 2 eΛ)
    let eK : kBar (L₀.map H₀.subtype) ≃* ↥S := eq1.symm.trans eL
    have hSc : Subgroup.center ↥S = ⊥ := center_eq_bot_of_simple' hS hSna
    have hmap : (Subgroup.center (kBar (L₀.map H₀.subtype))).map eK.toMonoidHom =
        Subgroup.center ↥S := Subgroup.map_center_eq eK
    rw [hSc] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective _ eK.injective).1 hmap
  ·
    have hρcm : ∀ l : ↥H₀, e.symm (ρ l) = centMap hKN hfC l := fun l => by
      simp [ρ]
    ext kb
    constructor
    · intro hkb
      obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hkb
      obtain ⟨l, hl, hlk⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hk)
      have hsS : ρ l ∈ S := by
        rw [← hL₀map]
        exact Subgroup.mem_map_of_mem _ hl
      refine Subgroup.mem_map.2 ⟨e.symm (ρ l), Subgroup.mem_map.2 ⟨ρ l, hsS, rfl⟩, ?_⟩
      show (((e.symm (ρ l)) : ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩))) : kBar K) =
        (QuotientGroup.mk k : kBar K)
      rw [hρcm, centMap_apply]
      congr 1
      exact Subtype.ext hlk
    · intro hkb
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hkb
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
      rw [← hL₀map] at hs
      obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.1 hs
      refine Subgroup.mem_map.2 ⟨⟨(l : G), l.2.1⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.2 (Subgroup.mem_map.2 ⟨l, hl, rfl⟩)
      · show (QuotientGroup.mk (⟨(l : G), l.2.1⟩ : ↥K) : kBar K) =
          (((e.symm (ρ l)) : ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩))) : kBar K)
        rw [hρcm, centMap_apply]
  ·
    intro c hc a ha
    have hcN : c ∈ normalizer (H₀ : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have hfc : ∀ y, y ∈ centralizer ({f} : Set G) → c * y * c⁻¹ ∈ centralizer ({f} : Set G) := by
        intro y hy
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hc.2 hy) (Subgroup.inv_mem _ hc.2)
      constructor
      · intro hh
        exact ⟨hKN c hc.1 h hh.1, hfc h hh.2⟩
      · intro hh
        have hcinv : c⁻¹ ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G) :=
          Subgroup.inv_mem _ hc
        have h1 := hKN c⁻¹ hcinv.1 (c * h * c⁻¹) hh.1
        have h2 : c⁻¹ * (c * h * c⁻¹) * c⁻¹⁻¹ = h := by group
        rw [h2] at h1
        have h3 : c⁻¹ * (c * h * c⁻¹) * c⁻¹⁻¹ ∈ centralizer ({f} : Set G) :=
          Subgroup.mul_mem _ (Subgroup.mul_mem _ hcinv.2 hh.2) (Subgroup.inv_mem _ hcinv.2)
        rw [h2] at h3
        exact ⟨h1, h3⟩
    let σc : ↥H₀ ≃* ↥H₀ := conjAut hcN
    have h2c : TwoComponents.IsTwoComponent (L₀.map σc.toMonoidHom) :=
      (TwoComponentTransport.equiv_iff σc L₀).mpr hL₀
    have hmapeq : L₀.map σc.toMonoidHom = L₀ := huniq _ h2c
    obtain ⟨l, hl, rfl⟩ := ha
    have hσl : σc l ∈ L₀ := hmapeq ▸ Subgroup.mem_map_of_mem _ hl
    exact ⟨σc l, hσl, rfl⟩
  ·
    intro a ha
    obtain ⟨y, hy, rfl⟩ := ha
    have hΛcore : (pPrimeCore 2 ↥L₀).map eΛ₀.toMonoidHom = pPrimeCore 2 ↥(L₀.map H₀.subtype) :=
      pPrimeCore_map_iso 2 eΛ₀
    rw [← hΛcore] at hy
    obtain ⟨l₀, hl₀, rfl⟩ := hy
    have h1 : l₀ ∈ ρL.ker := hcoreL₀ ▸ hl₀
    have h2 : ρ (l₀ : ↥H₀) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.1 h1)
    have h3 : centMap hKN hfC (l₀ : ↥H₀) = 1 :=
      e.injective (by simpa [ρ] using h2)
    have h4 : (QuotientGroup.mk (⟨((l₀ : ↥H₀) : G), (l₀ : ↥H₀).2.1⟩ : ↥K) : kBar K) = 1 := by
      have := congrArg Subtype.val h3
      rwa [centMap_apply] at this
    exact (IVK.Lifted.mem_pPrimeCoreOf_iff_hatMk K _).2 ⟨(l₀ : ↥H₀).2.1, h4⟩


section L2Case

theorem fixedPGL_sq_of_isFAut {Kb : Type} [Group Kb] [Finite Kb] (hL2 : HasL2Model Kb Odd)
    (h9 : ¬ HasL2Model Kb (fun q => q = 9)) {σ : MulAut Kb} (hσ : P34.IsFAutL2A7 Kb σ)
    (hσ2 : σ * σ = 1) :
    ∃ (F₀ : Type) (_ : Field F₀) (_ : Finite F₀), Odd (Nat.card F₀) ∧ 3 < Nat.card F₀ ∧
      HasL2Model Kb (fun q => q = Nat.card F₀ ^ 2) ∧
      Nonempty (↥(fixedSubgroup Kb σ) ≃* GorensteinWalter.PGL2 F₀) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : Kb ≃* L2 F), L2Field F ∧
        Nat.card F = Nat.card F₀ ^ 2 ∧ σ ∈ fieldAutSub e := by
  obtain ⟨F₁, _, _, hF₁, ⟨e₁⟩⟩ := exists_l2_model_of_hasL2Model hL2
  obtain ⟨hσ1, hcases⟩ := hσ
  rcases hcases with ⟨F, _, _, e, hFodd, hσF⟩ | ⟨⟨hA7⟩, -⟩
  swap
  · exact (Th2Tstar.not_hasL2Model_alt7 (fun q hq => hq) hA7 hL2).elim
  have hcard1 : Nat.card Kb = Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) / 2 := card_eq_of_L2Field e₁ hF₁
  have h60 : 60 ≤ Nat.card Kb := by
    rw [hcard1]
    obtain ⟨⟨t, ht⟩, h3⟩ := hF₁
    have h5 : 5 ≤ Nat.card F₁ := by omega
    have h25 : 25 ≤ Nat.card F₁ ^ 2 := by nlinarith
    have h24 : 24 ≤ Nat.card F₁ ^ 2 - 1 := by omega
    have : 5 * 24 ≤ Nat.card F₁ * (Nat.card F₁ ^ 2 - 1) := Nat.mul_le_mul h5 h24
    omega
  have hodd := isOddPrimePower_of_odd F hFodd
  have hcard : Nat.card Kb = Nat.card F * (Nat.card F ^ 2 - 1) / 2 := by
    rw [Nat.card_congr (toPSL e).toEquiv]
    exact GorensteinWalter.psl2_card_formula F hodd
  have hF3 : 3 < Nat.card F := by
    by_contra hle
    push Not at hle
    obtain ⟨m, hm⟩ := hFodd
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    have h3 : Nat.card F = 3 := by omega
    rw [hcard, h3] at h60
    norm_num at h60
  have hF : L2Field F := ⟨hFodd, hF3⟩
  have hF9 : Nat.card F ≠ 9 := fun h' => h9 (hasL2Model_nine h' e)
  obtain ⟨τ, rfl⟩ := hσF
  have hinj : Function.Injective (fieldAutHom e) := fun a b hab => by
    have := congrArg (fieldProj e) hab
    rwa [fieldProj_fieldAutHom, fieldProj_fieldAutHom] at this
  have hσord : orderOf (fieldAutHom e τ) = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hσ2) hσ1
  have hτ2 : orderOf τ = 2 := by
    rw [← orderOf_injective (fieldAutHom e) hinj τ]
    exact hσord
  obtain ⟨F₀, hF₀, hFin₀, hcard₀, ⟨eqv⟩⟩ :=
    (ivk_1_4a F hF Kb e τ).2.2 (by rw [hτ2]; exact even_two)
  rw [hτ2] at hcard₀
  have hodd₀ : Odd (Nat.card F₀) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    have : Even (Nat.card F) := by
      rw [← hcard₀]
      exact Nat.even_pow.2 ⟨hne, by norm_num⟩
    exact (Nat.not_even_iff_odd.2 hF.1) this
  have h3₀ : 3 < Nat.card F₀ := by
    by_contra hle
    push Not at hle
    have hq3 : 3 < Nat.card F := hF.2
    obtain ⟨m, hm⟩ := hodd₀
    interval_cases hq : Nat.card F₀
    · omega
    · have : Nat.card F = 1 := by rw [← hcard₀]; norm_num
      omega
    · omega
    · have : Nat.card F = 9 := by rw [← hcard₀]; norm_num
      exact hF9 this
  refine ⟨F₀, hF₀, hFin₀, hodd₀, h3₀, ?_, ⟨eqv⟩, F, inferInstance, inferInstance, e, hF, hcard₀.symm,
    ⟨τ, rfl⟩⟩
  have := hasL2Model_of_l2 hF e
  rwa [← hcard₀] at this

theorem layer_L2 {x f : G} {K : Subgroup G}
    (hKC : K ≤ centralizer ({x} : Set G))
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hfC : f ∈ centralizer ({x} : Set G)) (hf2 : orderOf f = 2)
    (hL2 : HasL2Model (kBar K) Odd) (h9 : ¬ HasL2Model (kBar K) (fun q => q = 9))
    (hσ : P34.IsFAutL2A7 (kBar K) (Back.actHom hKN ⟨f, hfC⟩)) :
    ∃ (r : ℕ) (Λ : Subgroup G), Odd r ∧ 5 ≤ r ∧ HasL2Model (kBar K) (fun q => q = r ^ 2) ∧
      IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G)) Λ ∧ Λ ≤ K ∧
      pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) = Λ ∧
      HasL2Model (kBar Λ) (fun q => q = r) ∧ Subgroup.center (kBar Λ) = ⊥ ∧
      IsL2 ↥((Λ.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K))) (fun q₀ => q₀ = r) ∧
      (∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G), ∀ a ∈ Λ, c * a * c⁻¹ ∈ Λ) ∧
      pPrimeCoreOf 2 Λ ≤ pPrimeCoreOf 2 K ∧
      ((Λ.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) =
        (_root_.commutator ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩))).map
          (fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)).subtype) ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (e : kBar K ≃* L2 F), L2Field F ∧
        Nat.card F = r ^ 2 ∧ Back.actHom hKN ⟨f, hfC⟩ ∈ fieldAutSub e := by
  classical
  have hσ2 : Back.actHom hKN ⟨f, hfC⟩ * Back.actHom hKN ⟨f, hfC⟩ = 1 := by
    rw [← map_mul]
    have : (⟨f, hfC⟩ * ⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one f
      rwa [hf2, sq] at this
    rw [this, map_one]
  obtain ⟨F₀, _, _, hodd, h3, hK2, ⟨e₀⟩, F, _, _, eF, hFF, hFcard, hαF⟩ := fixedPGL_sq_of_isFAut hL2 h9 hσ hσ2
  have hoddpp := isOddPrimePower_of_odd F₀ hodd
  let S : Subgroup (GorensteinWalter.PGL2 F₀) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := F₀)).range
  have hSn : S.Normal := Glauberman.Dickson.MaxSubfield.toPGL_range_normal hoddpp h3
  have hSq : CFSG.IsQuasisimple ↥S := ComponentClassification.CatalogueBLinearTwo.pglPSLRange_quasisimple F₀ h3
  have hSna : ∃ a b : ↥S, a * b ≠ b * a := exists_noncomm_of_quasisimple hSq
  let eS : GorensteinWalter.PSL2 F₀ ≃* ↥S :=
    MonoidHom.ofInjective Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
  have hSs : IsSimpleGroup ↥S := by
    have : IsSimpleGroup (GorensteinWalter.PSL2 F₀) :=
      Matrix.ProjectiveSpecialLinearGroup.rank_two_simple (by omega)
    exact eS.symm.isSimpleGroup
  have hperf : ∀ J : Subgroup (GorensteinWalter.PGL2 F₀), J ≠ ⊥ → ⁅J, J⁆ = J → J.IsSubnormal → J = S := by
    intro J hJ hJp hJs
    exact (GorensteinWalter.pgl2_perfect_subnormal_eq_commutator F₀ hoddpp J hJ
      (Subgroup.isPerfect_iff.mpr hJp) hJs).2.trans
      (GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three F₀ hoddpp h3)
  have := hSn
  obtain ⟨Λ, hΛ, hΛK, hlay, ⟨eΛ⟩, hcen, himg, hΛW, hΛc⟩ :=
    layer_data hKC hKN hfC hf2 e₀ S hSs hSna hperf
  have hF₀ : L2Field F₀ := ⟨hodd, h3⟩
  refine ⟨Nat.card F₀, Λ, hodd, by obtain ⟨m, hm⟩ := hodd; omega, hK2, hΛ, hΛK, hlay,
    hasL2Model_of_l2 hF₀ (eΛ.trans (eS.symm.trans (L2.equivPSL F₀).symm)), hcen, ?_, hΛW, hΛc, ?_,
    F, inferInstance, inferInstance, eF, hFF, hFcard, hαF⟩
  swap
  · rw [himg]
    congr 1
    have hScomm : S = _root_.commutator (GorensteinWalter.PGL2 F₀) :=
      (GorensteinWalter.pgl2_commutator_eq_psl2_range_of_card_gt_three F₀ hoddpp h3).symm
    rw [hScomm, _root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e₀.symm.surjective]
  refine ⟨F₀, inferInstance, inferInstance, rfl, ⟨?_⟩⟩
  rw [himg]
  let e1 : ↥S ≃* ↥(S.map e₀.symm.toMonoidHom) :=
    Subgroup.equivMapOfInjective S e₀.symm.toMonoidHom e₀.symm.injective
  let e2 : ↥(S.map e₀.symm.toMonoidHom) ≃*
      ↥((S.map e₀.symm.toMonoidHom).map (fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)).subtype) :=
    Subgroup.equivMapOfInjective _ (fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)).subtype
      (fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)).subtype_injective
  exact (e1.trans e2).symm.trans (eS.symm.trans (L2.equivPSL F₀).symm)

end L2Case


section A7Case

theorem eq_bot_or_eq_top_of_isSubnormal {Q : Type*} [Group Q] [IsSimpleGroup Q] {J : Subgroup Q}
    (hJ : J.IsSubnormal) : J = ⊥ ∨ J = ⊤ := by
  induction hJ with
  | top => exact Or.inr rfl
  | step lower upper hle hup hnorm ih =>
    rcases ih with h | h
    · left
      exact eq_bot_iff.2 (h ▸ hle)
    · rw [h] at hnorm
      have hN : lower.Normal := ⟨fun n hn g => by
        have h1 : (⟨n, trivial⟩ : ↥(⊤ : Subgroup Q)) ∈ lower.subgroupOf ⊤ := hn
        have h2 := hnorm.conj_mem _ h1 ⟨g, trivial⟩
        exact h2⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal lower

theorem perfect_subnormal_eq_commutator {Ω : Type*} [Group Ω] (hA : IsSimpleGroup ↥(_root_.commutator Ω))
    (J : Subgroup Ω) (hJ : J ≠ ⊥) (hp : ⁅J, J⁆ = J) (hs : J.IsSubnormal) : J = _root_.commutator Ω := by
  have hJA : J ≤ _root_.commutator Ω := by
    rw [← hp]
    exact Subgroup.commutator_mono le_top le_top
  have hs' : (J.subgroupOf (_root_.commutator Ω)).IsSubnormal := hs.subgroupOf
  rcases eq_bot_or_eq_top_of_isSubnormal hs' with h | h
  · exfalso
    apply hJ
    rw [← Subgroup.map_subgroupOf_eq_of_le hJA, h, Subgroup.map_bot]
  · refine le_antisymm hJA ?_
    intro a ha
    have : (⟨a, ha⟩ : ↥(_root_.commutator Ω)) ∈ J.subgroupOf (_root_.commutator Ω) := by rw [h]; trivial
    exact this

theorem isSolvable_cent_of_fixed {x f : G} {K : Subgroup G}
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hfC : f ∈ centralizer ({x} : Set G))
    (hsolv : Group.IsSolvable ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩))) :
    Group.IsSolvable ↥(K ⊓ centralizer ({f} : Set G)) := by
  have hk : Group.IsSolvable ↥(centMap hKN hfC).ker :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (centMap_ker_odd hKN hfC)
  exact Group.isSolvable_of_ker_le_range (centMap hKN hfC).ker.subtype (centMap hKN hfC)
    (fun y hy => ⟨⟨y, hy⟩, rfl⟩)

theorem layer_A7 {x f : G} {K : Subgroup G}
    (hKC : K ≤ centralizer ({x} : Set G))
    (hKN : ∀ c ∈ centralizer ({x} : Set G), ∀ k ∈ K, c * k * c⁻¹ ∈ K)
    (hfC : f ∈ centralizer ({x} : Set G)) (hf2 : orderOf f = 2)
    (e7 : kBar K ≃* alternatingGroup (Fin 7))
    (hout : Back.actHom hKN ⟨f, hfC⟩ ∉ innAut (kBar K))
    (hlayer : pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) ≠ ⊥) :
    ∃ Λ : Subgroup G, IsPCompIn 2 (centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G)) Λ ∧
      Λ ≤ K ∧ pLayerOf 2 (K ⊓ centralizer ({f} : Set G)) = Λ ∧
      HasL2Model (kBar Λ) (fun q => q = 5) ∧ Subgroup.center (kBar Λ) = ⊥ ∧
      (psiEquiv e7 (Back.actHom hKN ⟨f, hfC⟩)).cycleType = {2} ∧
      ((Λ.subgroupOf K).map (QuotientGroup.mk' (pPrimeCore 2 ↥K)) =
        (_root_.commutator ↥(fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩))).map
          (fixedSubgroup (kBar K) (Back.actHom hKN ⟨f, hfC⟩)).subtype) ∧
      (∀ c ∈ centralizer ({x} : Set G) ⊓ centralizer ({f} : Set G), ∀ a ∈ Λ, c * a * c⁻¹ ∈ Λ) ∧
      pPrimeCoreOf 2 Λ ≤ pPrimeCoreOf 2 K := by
  classical
  set α := Back.actHom hKN ⟨f, hfC⟩ with hα
  have hα2 : α * α = 1 := by
    rw [hα, ← map_mul]
    have : (⟨f, hfC⟩ * ⟨f, hfC⟩ : ↥(centralizer ({x} : Set G))) = 1 := by
      apply Subtype.ext
      have := pow_orderOf_eq_one f
      rwa [hf2, sq] at this
    rw [this, map_one]
  set ψ := psiEquiv e7 α with hψ
  have hψ2 : ψ * ψ = 1 := by rw [hψ, ← map_mul, hα2, map_one]
  have hψ1 : ψ ≠ 1 := by
    intro h
    apply hout
    have : α = 1 := (psiEquiv e7).injective (by rw [← hψ, h, map_one])
    rw [this]
    exact (innAut (kBar K)).one_mem
  have hψodd : ψ ∉ alternatingGroup (Fin 7) := by
    intro h
    apply hout
    rw [← psi_map_innAut e7] at h
    obtain ⟨a, ha, hae⟩ := h
    have : a = α := (psiEquiv e7).injective hae
    rwa [this] at ha
  have hψord : orderOf ψ = 2 := orderOf_eq_prime (by rw [sq]; exact hψ2) hψ1
  obtain ⟨eC⟩ := fixedSubgroup_equiv_A7 e7 α
  rcases odd_involution_cycleType hψord hψodd with hct | hct
  swap
  · exfalso
    apply hlayer
    obtain ⟨e4⟩ := IVK.A7.centralizer_A7_two_two_two_equiv hct
    have h4 : Group.IsSolvable (Equiv.Perm (Fin 4)) := Equiv.Perm.isSolvable (by simp)
    have hfs : Group.IsSolvable ↥(fixedSubgroup (kBar K) α) :=
      Group.isSolvable_of_isSolvable_injective (f := (eC.trans e4).toMonoidHom) (eC.trans e4).injective
    exact pLayerOf_eq_bot_of_solvable (isSolvable_cent_of_fixed hKN hfC hfs)
  obtain ⟨e5⟩ := IVK.A7.centralizer_A7_swap_equiv (Equiv.Perm.isSwap_iff_cycleType.mpr hct)
  let e : ↥(fixedSubgroup (kBar K) α) ≃* Equiv.Perm (Fin 5) := eC.trans e5
  have h5 : 5 ≤ Nat.card (Fin 5) := by simp
  have hAs : IsSimpleGroup ↥(_root_.commutator (Equiv.Perm (Fin 5))) := by
    rw [alternatingGroup.commutator_perm_eq h5]
    exact alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin])
  have hAna : ∃ a b : ↥(_root_.commutator (Equiv.Perm (Fin 5))), a * b ≠ b * a := by
    rw [alternatingGroup.commutator_perm_eq h5]
    exact alt5_exists_noncomm
  have : (_root_.commutator (Equiv.Perm (Fin 5))).Normal := inferInstance
  obtain ⟨Λ, hΛ, hΛK, hlay, ⟨eΛ⟩, hcen, himg, hΛW, hΛc⟩ :=
    layer_data hKC hKN hfC hf2 e (_root_.commutator (Equiv.Perm (Fin 5))) hAs hAna
      (fun J hJ hp hs => perfect_subnormal_eq_commutator hAs J hJ hp hs)
  refine ⟨Λ, hΛ, hΛK, hlay, ?_, hcen, hct, ?_, hΛW, hΛc⟩
  · refine ⟨5, 1, Nat.prime_five, le_rfl, by norm_num, ?_⟩
    have eA : kBar Λ ≃* alternatingGroup (Fin 5) :=
      eΛ.trans (MulEquiv.subgroupCongr (alternatingGroup.commutator_perm_eq h5))
    exact CFSG.GH74.E2.lieModel_psl_two_five_of_alt ⟨eA⟩
  · rw [himg]
    congr 1
    have h1 : (_root_.commutator (Equiv.Perm (Fin 5))).map e.symm.toMonoidHom =
        _root_.commutator ↥(fixedSubgroup (kBar K) α) := by
      rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ e.symm.surjective]
    exact h1

end A7Case

end CFSG.GH74.GLS.C3.Layer1.Thm1L32
