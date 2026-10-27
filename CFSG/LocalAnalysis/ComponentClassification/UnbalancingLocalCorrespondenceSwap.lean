module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalCorrespondenceTools
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSASwappedCentralProduct

public noncomputable section

namespace CFSG.ComponentClassification.UnbalancingLocal

open Subgroup CFSG.ComponentClassification.UnbalancedGS

namespace Correspondence

variable {H : Type*} [Group H] [Finite H]

theorem not_two_dvd_card_ker_restrict (V : Subgroup H) :
    ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (pPrimeCore 2 H)).domRestrict V).ker := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcop : Nat.Coprime 2 (Nat.card (QuotientGroup.mk' (pPrimeCore 2 H)).ker) := by
    rw [QuotientGroup.ker_mk']
    exact pPrimeCore_coprime_card
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp
    (CatalogueBPrimeJoin.coprime_card_restriction_kernel 2 _ hcop V)

theorem image_components {L₁ L₂ : Subgroup H} (h₁ : IsPComponent 2 L₁) (h₂ : IsPComponent 2 L₂)
    (hne : L₁ ≠ L₂) :
    IsComponent (L₁.map (QuotientGroup.mk' (pPrimeCore 2 H))) ∧
      IsComponent (L₂.map (QuotientGroup.mk' (pPrimeCore 2 H))) ∧
      L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≠ L₂.map (QuotientGroup.mk' (pPrimeCore 2 H)) ∧
      ∀ x ∈ L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)),
        ∀ y ∈ L₂.map (QuotientGroup.mk' (pPrimeCore 2 H)), x * y = y * x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbij := (CatalogueBPrimeJoin.canonical_prime_component_lift (p := 2) (X := H)).2
  have hA := hbij.mapsTo h₁
  have hB := hbij.mapsTo h₂
  have hAB : L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ≠
      L₂.map (QuotientGroup.mk' (pPrimeCore 2 H)) := fun heq => hne (hbij.injOn h₁ h₂ heq)
  refine ⟨hA, hB, hAB, ?_⟩
  rcases CFSG.LocalCores.distinct_components_commute hA hB with h | h
  · exact absurd h hAB
  · intro x hx y hy
    have h1 := Subgroup.commutator_mem_commutator hx hy
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1

theorem pPrimeCore_eq_bot_of_isComponent {A : Subgroup (H ⧸ pPrimeCore 2 H)}
    (hA : IsComponent A) : pPrimeCore 2 A = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CatalogueBHeldSmallCore.primeCore_subnormal_intersection 2 A hA.2,
    pPrimeCore_quotient_pPrimeCore_eq_bot, Subgroup.bot_subgroupOf]

theorem card_image_eq {L₁ : Subgroup H} (h₁ : IsPComponent 2 L₁) :
    Nat.card (L₁.map (QuotientGroup.mk' (pPrimeCore 2 H))) = Nat.card (L₁ ⧸ pPrimeCore 2 L₁) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨e, -⟩ := CatalogueBPrimeJoin.exists_restrict_core_quotient_equiv (p := 2)
    (QuotientGroup.mk' (pPrimeCore 2 H)) L₁ (not_two_dvd_card_ker_restrict L₁)
  have hA := (CatalogueBPrimeJoin.canonical_prime_component_lift (p := 2) (X := H)).2.mapsTo h₁
  have hcore := pPrimeCore_eq_bot_of_isComponent hA
  calc Nat.card (L₁.map (QuotientGroup.mk' (pPrimeCore 2 H))) =
        Nat.card ((L₁.map (QuotientGroup.mk' (pPrimeCore 2 H))) ⧸
          pPrimeCore 2 (L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)))) :=
        Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hcore).trans
          QuotientGroup.quotientBot).toEquiv.symm
    _ = Nat.card (L₁ ⧸ pPrimeCore 2 L₁) := (Nat.card_congr e.toEquiv).symm

theorem exists_swap {Q : Type*} [Group Q] {A B : Subgroup Q} {g : Q} (hg : g * g = 1)
    (hAB : A.map (MulAut.conj g).toMonoidHom = B) :
    ∃ α : ↥(A ⊔ B) ≃* ↥(A ⊔ B), (∀ k, (α k : Q) = g * k * g⁻¹) ∧ (∀ k, α (α k) = k) ∧
      (A.subgroupOf (A ⊔ B)).map α.toMonoidHom = B.subgroupOf (A ⊔ B) := by
  have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hg
  have hconj2 : ∀ x : Q, g * (g * x * g⁻¹) * g⁻¹ = x := fun x => by
    rw [hginv]
    calc g * (g * x * g) * g = (g * g) * x * (g * g) := by group
      _ = x := by rw [hg, one_mul, mul_one]
  have hBA : B.map (MulAut.conj g).toMonoidHom = A := by
    rw [← hAB, Subgroup.map_map]
    convert Subgroup.map_id A
    ext x
    exact hconj2 x
  have hsup : (A ⊔ B).map (MulAut.conj g).toMonoidHom = A ⊔ B := by
    rw [Subgroup.map_sup, hAB, hBA, sup_comm]
  refine ⟨((MulAut.conj g).subgroupMap (A ⊔ B)).trans (MulEquiv.subgroupCongr hsup),
    fun k => rfl, fun k => Subtype.ext (hconj2 k), ?_⟩
  ext k
  constructor
  · rintro ⟨k', hk', rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk'
    rw [Subgroup.mem_subgroupOf]
    change g * (k' : Q) * g⁻¹ ∈ B
    have h1 : g * (k' : Q) * g⁻¹ ∈ A.map (MulAut.conj g).toMonoidHom := ⟨k', hk', rfl⟩
    rwa [hAB] at h1
  · intro hk
    rw [Subgroup.mem_subgroupOf] at hk
    have hmem : g * (k : Q) * g⁻¹ ∈ A ⊔ B := by
      have h1 : g * (k : Q) * g⁻¹ ∈ (A ⊔ B).map (MulAut.conj g).toMonoidHom := ⟨k, k.2, rfl⟩
      rwa [hsup] at h1
    refine ⟨⟨g * k * g⁻¹, hmem⟩, ?_, Subtype.ext (hconj2 k)⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    change g * (k : Q) * g⁻¹ ∈ A
    have h1 : g * (k : Q) * g⁻¹ ∈ B.map (MulAut.conj g).toMonoidHom := ⟨k, hk, rfl⟩
    rwa [hBA] at h1

theorem exists_fixed_lift {K : Subgroup H} {a : H} (ha2 : a * a = 1)
    (haK : a ∈ normalizer (K : Set H)) {y : H ⧸ pPrimeCore 2 H}
    (hy : y ∈ K.map (QuotientGroup.mk' (pPrimeCore 2 H)))
    (hfix : (a : H ⧸ pPrimeCore 2 H) * y * (a : H ⧸ pPrimeCore 2 H)⁻¹ = y) :
    ∃ x ∈ K, a * x = x * a ∧ (x : H ⧸ pPrimeCore 2 H) = y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hzp : ∀ c ∈ zpowers a, c = 1 ∨ c = a := by
    intro c hc
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hc
    rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
    · left
      rw [zpow_mul, zpow_two, ha2, one_zpow]
    · right
      rw [zpow_add, zpow_mul, zpow_two, ha2, one_zpow, one_mul, zpow_one]
  have hBN : zpowers a ≤ normalizer (K : Set H) := zpowers_le.mpr haK
  let α : zpowers a →* MulAut K := K.normalizerMonoidHom.comp (Subgroup.inclusion hBN)
  have hα : ∀ (c : zpowers a) (k : K), ((α c k : K) : H) = (c : H) * k * (c : H)⁻¹ :=
    fun c k => Subgroup.normalizerMonoidHom_apply_apply_coe K _ k
  have hA2 : IsPGroup 2 (zpowers a) := fun c => ⟨1, Subtype.ext (by
    rcases hzp c c.2 with hc | hc
    · rw [Subgroup.coe_pow, hc, one_pow, Subgroup.coe_one]
    · rw [Subgroup.coe_pow, hc, pow_one, pow_two, ha2, Subgroup.coe_one])⟩
  have hNn : ((pPrimeCore 2 H).subgroupOf K).Normal :=
    (inferInstance : (pPrimeCore 2 H).Normal).subgroupOf K
  have hN : ∀ c : zpowers a, ∀ n ∈ (pPrimeCore 2 H).subgroupOf K,
      α c n ∈ (pPrimeCore 2 H).subgroupOf K := by
    intro c n hn
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    rw [hα]
    exact (inferInstance : (pPrimeCore 2 H).Normal).conj_mem _ hn _
  have hcop : ¬ 2 ∣ Nat.card ((pPrimeCore 2 H).subgroupOf K) := by
    intro h2
    have hdvd : Nat.card ((pPrimeCore 2 H).subgroupOf K) ∣ Nat.card (pPrimeCore 2 H) := by
      let φ : (pPrimeCore 2 H).subgroupOf K →* pPrimeCore 2 H :=
        { toFun := fun n => ⟨((n : K) : H), n.2⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hinj : Function.Injective φ := by
        intro n m hnm
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun x : pPrimeCore 2 H => (x : H)) hnm
      exact Subgroup.card_dvd_of_injective φ hinj
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp pPrimeCore_coprime_card
      (h2.trans hdvd)
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 2 hA2 α
    ((pPrimeCore 2 H).subgroupOf K) hN hcop
  obtain ⟨k, hk, rfl⟩ := hy
  have hfix' : (a : H ⧸ pPrimeCore 2 H) * (k : H ⧸ pPrimeCore 2 H) *
      (a : H ⧸ pPrimeCore 2 H)⁻¹ = (k : H ⧸ pPrimeCore 2 H) := hfix
  have hq : ((⟨k, hk⟩ : K) : K ⧸ (pPrimeCore 2 H).subgroupOf K) ∈
      {q | ∀ c : zpowers a, CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction α
        ((pPrimeCore 2 H).subgroupOf K) hN c q = q} := by
    intro c
    rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk, eq_comm,
      QuotientGroup.eq, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hα]
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    rcases hzp c c.2 with hc | hc
    · rw [hc, QuotientGroup.mk_one, one_mul, inv_one, mul_one, inv_mul_cancel]
    · rw [hc]
      change ((k : H) : H ⧸ pPrimeCore 2 H)⁻¹ * ((a : H ⧸ pPrimeCore 2 H) *
        (k : H ⧸ pPrimeCore 2 H) * (a : H ⧸ pPrimeCore 2 H)⁻¹) = 1
      rw [hfix', inv_mul_cancel]
  rw [hlift] at hq
  obtain ⟨x, hxfix, hxq⟩ := hq
  refine ⟨x, x.2, ?_, ?_⟩
  · have h1 := congrArg Subtype.val (hxfix ⟨a, mem_zpowers a⟩)
    rw [hα] at h1
    exact mul_inv_eq_iff_eq_mul.mp h1
  · have h1 := QuotientGroup.eq.mp hxq
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h1
    change ((x : H) : H ⧸ pPrimeCore 2 H) = (k : H ⧸ pPrimeCore 2 H)
    exact (QuotientGroup.eq.mpr h1)

theorem swap_layer_analysis {L₁ L₂ : Subgroup H} (h₁ : IsPComponent 2 L₁)
    (h₂ : IsPComponent 2 L₂) (hne : L₁ ≠ L₂) {a : H} (ha2 : a * a = 1)
    (hL₂ : L₂ = L₁.map (MulAut.conj a).toMonoidHom) (A B : Subgroup (H ⧸ pPrimeCore 2 H))
    (hAdef : A = L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)))
    (hBdef : B = L₂.map (QuotientGroup.mk' (pPrimeCore 2 H))) (T₀ : Subgroup H)
    (hT₀ : T₀ = gsFixedLayer (L₁ ⊔ L₂) a) :
    ∃ α : ↥(A ⊔ B) ≃* ↥(A ⊔ B),
      (∀ k, (α k : H ⧸ pPrimeCore 2 H) =
        (a : H ⧸ pPrimeCore 2 H) * k * (a : H ⧸ pPrimeCore 2 H)⁻¹) ∧
      A ≠ B ∧ (∀ x ∈ A, ∀ y ∈ B, x * y = y * x) ∧ IsQuasisimple A ∧ IsQuasisimple B ∧
      (∀ d ∈ A ⊓ B, ∀ k ∈ A ⊔ B, d * k = k * d) ∧ IsPGroup 2 ↥(A ⊓ B) ∧
      (∀ x, x ∈ T₀.map (QuotientGroup.mk' (pPrimeCore 2 H)) ↔
        ∃ u : ↥(A ⊔ B), (u : H ⧸ pPrimeCore 2 H) ∈ A ∧ x = ((u * α u : ↥(A ⊔ B)) : _)) ∧
      (∃ e : T₀ ⧸ pPrimeCore 2 T₀ ≃* ↥(T₀.map (QuotientGroup.mk' (pPrimeCore 2 H))),
        ∀ t : T₀, (e t : H ⧸ pPrimeCore 2 H) = ((t : H) : H ⧸ pPrimeCore 2 H)) ∧
      Nat.card (T₀ ⧸ pPrimeCore 2 T₀) = Nat.card (L₁ ⧸ pPrimeCore 2 L₁) /
        Nat.card {d : ↥(A ⊔ B) // (d : H ⧸ pPrimeCore 2 H) ∈ A ⊓ B ∧ α d = d⁻¹} ∧
      (Nat.card (T₀ ⧸ pPrimeCore 2 T₀) = Nat.card (L₁ ⧸ pPrimeCore 2 L₁) ↔ A ⊓ B = ⊥) ∧
      (A ⊓ B = ⊥ → (∃ e : ↥A × ↥B ≃* ↥(A ⊔ B), ∀ x y, (e (x, y) : H ⧸ pPrimeCore 2 H) = x * y) ∧
        ∀ x, x ∈ T₀.map (QuotientGroup.mk' (pPrimeCore 2 H)) ↔
          ∃ k : ↥(A ⊔ B), α k = k ∧ x = k) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst hAdef hBdef hT₀
  obtain ⟨hA, hB, hAB, hcomm⟩ := image_components h₁ h₂ hne
  have hconjπ : (QuotientGroup.mk' (pPrimeCore 2 H)).comp (MulAut.conj a).toMonoidHom =
      (MulAut.conj ((a : H ⧸ pPrimeCore 2 H))).toMonoidHom.comp
        (QuotientGroup.mk' (pPrimeCore 2 H)) := by
    ext x
    simp [MulAut.conj_apply]
  have hAB' : (L₁.map (QuotientGroup.mk' (pPrimeCore 2 H))).map
      (MulAut.conj ((a : H ⧸ pPrimeCore 2 H))).toMonoidHom =
      L₂.map (QuotientGroup.mk' (pPrimeCore 2 H)) := by
    rw [hL₂, Subgroup.map_map, Subgroup.map_map, hconjπ]
  have hg : (a : H ⧸ pPrimeCore 2 H) * (a : H ⧸ pPrimeCore 2 H) = 1 := by
    rw [← QuotientGroup.mk_mul, ha2, QuotientGroup.mk_one]
  obtain ⟨α, hαk, hα2, hαA⟩ := exists_swap hg hAB'
  have hcoreA := pPrimeCore_eq_bot_of_isComponent hA
  set C : Subgroup ↥(L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊔
      L₂.map (QuotientGroup.mk' (pPrimeCore 2 H))) :=
    MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id _) with hCdef
  have hC : ∀ k, k ∈ C ↔ α k = k := fun k => Iff.rfl
  obtain ⟨-, hDcent, hD2, δ, hδ, hδker, -, -, -, hΔcore, -, hlayer, hcard, -, hcardiff, hcase⟩ :=
    swapped_central_product_fixed_layer _ _ hcomm hA.1 hcoreA α hα2 hαA C hC
  have hconj2 : ∀ x : H, a * (a * x * a⁻¹) * a⁻¹ = x := fun x => by
    have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
    rw [hainv]
    calc a * (a * x * a) * a = (a * a) * x * (a * a) := by group
      _ = x := by rw [ha2, one_mul, mul_one]
  have hL₁ : L₂.map (MulAut.conj a).toMonoidHom = L₁ := by
    rw [hL₂, Subgroup.map_map]
    convert Subgroup.map_id L₁
    ext x
    exact hconj2 x
  have haK : a ∈ normalizer ((L₁ ⊔ L₂ : Subgroup H) : Set H) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup]
    have e1 : L₁.map (MulAut.conj a : H →* H) = L₂ := hL₂.symm
    have e2 : L₂.map (MulAut.conj a : H →* H) = L₁ := hL₁
    rw [e1, e2, sup_comm]
  set F := (L₁ ⊔ L₂) ⊓ centralizer ({a} : Set H) with hFdef
  have hsupmap : (L₁ ⊔ L₂).map (QuotientGroup.mk' (pPrimeCore 2 H)) =
      L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊔ L₂.map (QuotientGroup.mk' (pPrimeCore 2 H)) :=
    Subgroup.map_sup _ _ _
  have hmem1 : ∀ x : F, (QuotientGroup.mk' (pPrimeCore 2 H)).comp F.subtype x ∈
      L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊔
        L₂.map (QuotientGroup.mk' (pPrimeCore 2 H)) := fun x => by
    rw [← hsupmap]
    exact ⟨x, x.2.1, rfl⟩
  let ψ₀ := ((QuotientGroup.mk' (pPrimeCore 2 H)).comp F.subtype).codRestrict _ hmem1
  have hψ₀C : ∀ x, ψ₀ x ∈ C := fun x => by
    rw [hC]
    apply Subtype.ext
    rw [hαk]
    have hx : (x : H) * a = a * (x : H) := mem_centralizer_singleton_iff.mp x.2.2
    change (a : H ⧸ pPrimeCore 2 H) * ((x : H) : H ⧸ pPrimeCore 2 H) *
      (a : H ⧸ pPrimeCore 2 H)⁻¹ = ((x : H) : H ⧸ pPrimeCore 2 H)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul, ← hx,
      mul_inv_cancel_right]
  let ψ : F →* C := ψ₀.codRestrict C hψ₀C
  have hψsurj : Function.Surjective ψ := by
    rintro ⟨c, hc⟩
    have hy : (c : H ⧸ pPrimeCore 2 H) ∈ (L₁ ⊔ L₂).map (QuotientGroup.mk' (pPrimeCore 2 H)) := by
      rw [hsupmap]
      exact c.2
    have hfix : (a : H ⧸ pPrimeCore 2 H) * (c : H ⧸ pPrimeCore 2 H) *
        (a : H ⧸ pPrimeCore 2 H)⁻¹ = (c : H ⧸ pPrimeCore 2 H) := by
      rw [← hαk, (hC c).mp hc]
    obtain ⟨x, hxK, hxa, hxc⟩ := exists_fixed_lift ha2 haK hy hfix
    refine ⟨⟨x, hxK, mem_centralizer_singleton_iff.mpr hxa.symm⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hxc
  have hψker : ¬ 2 ∣ Nat.card ψ.ker := by
    rw [MonoidHom.ker_codRestrict, MonoidHom.ker_codRestrict]
    exact not_two_dvd_card_ker_restrict F
  have hlayerF : (pLayer F 2).map ψ = pLayer C 2 := map_pLayer_of_coprime_kernel ψ hψsurj hψker
  have himage : (gsFixedLayer (L₁ ⊔ L₂) a).map (QuotientGroup.mk' (pPrimeCore 2 H)) =
      δ.range.map (L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊔
        L₂.map (QuotientGroup.mk' (pPrimeCore 2 H))).subtype := by
    have hcomp : (QuotientGroup.mk' (pPrimeCore 2 H)).comp F.subtype =
        (((L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊔
          L₂.map (QuotientGroup.mk' (pPrimeCore 2 H))).subtype).comp C.subtype).comp ψ := by
      ext x
      rfl
    rw [gsFixedLayer, Subgroup.map_map, hcomp, ← Subgroup.map_map, hlayerF, ← Subgroup.map_map,
      hlayer]
  have hmemT : ∀ x, x ∈ (gsFixedLayer (L₁ ⊔ L₂) a).map (QuotientGroup.mk' (pPrimeCore 2 H)) ↔
      ∃ u : ↥(L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊔
        L₂.map (QuotientGroup.mk' (pPrimeCore 2 H))),
        (u : H ⧸ pPrimeCore 2 H) ∈ L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ∧
          x = ((u * α u : ↥(L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊔
            L₂.map (QuotientGroup.mk' (pPrimeCore 2 H)))) : _) := by
    intro x
    rw [himage]
    constructor
    · rintro ⟨k, ⟨u, rfl⟩, rfl⟩
      refine ⟨Subgroup.inclusion le_sup_left u, u.2, ?_⟩
      rw [hδ u]
      rfl
    · rintro ⟨u, hu, rfl⟩
      refine ⟨u * α u, ⟨⟨u, hu⟩, ?_⟩, rfl⟩
      rw [hδ]
      rfl
  have hΔiso : δ.range ≃*
      ↥((gsFixedLayer (L₁ ⊔ L₂) a).map (QuotientGroup.mk' (pPrimeCore 2 H))) :=
    (δ.range.equivMapOfInjective _ (Subgroup.subtype_injective _)).trans
      (MulEquiv.subgroupCongr himage.symm)
  have hcoreT : pPrimeCore 2
      ↥((gsFixedLayer (L₁ ⊔ L₂) a).map (QuotientGroup.mk' (pPrimeCore 2 H))) = ⊥ := by
    rw [← pPrimeCore_map_iso 2 hΔiso, hΔcore, Subgroup.map_bot]
  have hfT := (QuotientGroup.mk' (pPrimeCore 2 H)).subgroupMap_surjective
    (gsFixedLayer (L₁ ⊔ L₂) a)
  have hfTker : ¬ 2 ∣ Nat.card ((QuotientGroup.mk' (pPrimeCore 2 H)).subgroupMap
      (gsFixedLayer (L₁ ⊔ L₂) a)).ker := by
    have heq : ((QuotientGroup.mk' (pPrimeCore 2 H)).subgroupMap
        (gsFixedLayer (L₁ ⊔ L₂) a)).ker =
        ((QuotientGroup.mk' (pPrimeCore 2 H)).domRestrict (gsFixedLayer (L₁ ⊔ L₂) a)).ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩
    rw [heq]
    exact not_two_dvd_card_ker_restrict _
  obtain ⟨-, e, he⟩ := exists_quotient_equiv_of_coprime_kernel _ hfT hfTker hcoreT
  have hcardT : Nat.card (gsFixedLayer (L₁ ⊔ L₂) a ⧸ pPrimeCore 2 (gsFixedLayer (L₁ ⊔ L₂) a)) =
      Nat.card (pLayer C 2) := by
    rw [Nat.card_congr e.toEquiv, ← Nat.card_congr hΔiso.toEquiv]
    exact (Nat.card_congr (((pLayer C 2).equivMapOfInjective C.subtype
      C.subtype_injective).trans (MulEquiv.subgroupCongr hlayer)).toEquiv).symm
  have hcardA := card_image_eq h₁
  have hcardD : Nat.card δ.ker = Nat.card {d : ↥(L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊔
      L₂.map (QuotientGroup.mk' (pPrimeCore 2 H))) //
      (d : H ⧸ pPrimeCore 2 H) ∈ L₁.map (QuotientGroup.mk' (pPrimeCore 2 H)) ⊓
        L₂.map (QuotientGroup.mk' (pPrimeCore 2 H)) ∧ α d = d⁻¹} := by
    refine Nat.card_congr
      { toFun := fun u => ⟨Subgroup.inclusion le_sup_left u.1,
          Subgroup.mem_inf.mpr ⟨u.1.2, ((hδker u.1).mp u.2).1⟩, ((hδker u.1).mp u.2).2⟩
        invFun := fun d => ⟨⟨d.1, (Subgroup.mem_inf.mp d.2.1).1⟩,
          (hδker _).mpr ⟨(Subgroup.mem_inf.mp d.2.1).2, d.2.2⟩⟩
        left_inv := fun u => rfl
        right_inv := fun d => rfl }
  refine ⟨α, hαk, hAB, hcomm, hA.1, hB.1, hDcent, hD2, hmemT, ⟨e, fun t => by rw [he]; rfl⟩,
    ?_, ?_, ?_⟩
  · rw [hcardT, hcard, hcardA, hcardD]
  · rw [hcardT, ← hcardA]
    exact hcardiff
  · intro hD
    obtain ⟨eAB, hCeq, -⟩ := hcase hD
    refine ⟨eAB, fun x => ?_⟩
    rw [himage, ← hCeq]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, (hC k).mp hk, rfl⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨k, (hC k).mpr hk, rfl⟩

end Correspondence

end CFSG.ComponentClassification.UnbalancingLocal
