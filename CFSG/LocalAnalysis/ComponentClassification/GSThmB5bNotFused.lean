module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmBCatalog5A10
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bL34Tools
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma513
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bPerfectAction
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bInputsB
public import CFSG.LocalAnalysis.ComponentClassification.GSLitChain
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierAlternating

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise

theorem mem_of_sylow_of_le_normalizer {G : Type*} [Group G] [Finite G] {Y B : Subgroup G}
    (hYN : Y ≤ normalizer (B : Set G))
    (hS : ∃ R : Sylow 2 ↥Y, (R : Subgroup ↥Y) = B.subgroupOf Y) {e : G} (he : e ∈ Y)
    {k : ℕ} (hek : e ^ 2 ^ k = 1) : e ∈ B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨R, hR⟩ := hS
  have hRn : (R : Subgroup ↥Y).Normal := by
    rw [hR]
    refine ⟨fun n hn g => ?_⟩
    rw [mem_subgroupOf] at hn ⊢
    have := (mem_normalizer_iff.mp (hYN g.2) n).mp hn
    simpa using this
  have hx : (⟨e, he⟩ : ↥Y) ^ 2 ^ k = 1 := Subtype.ext (by simpa using hek)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hx)
  have hE : IsPGroup 2 (zpowers (⟨e, he⟩ : ↥Y)) :=
    IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
  obtain ⟨Q, hQ⟩ := hE.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq ↥Y R Q
  have hRQ : Q = R := by
    rw [← hg]
    exact Sylow.smul_eq_of_normal
  have hmem : (⟨e, he⟩ : ↥Y) ∈ (R : Subgroup ↥Y) := by
    rw [← hRQ]
    exact hQ (mem_zpowers _)
  rw [hR, mem_subgroupOf] at hmem
  exact hmem

theorem eq_top_of_index_lt_of_pComponent {G : Type} [Group G] [Finite G] {L Y : Subgroup G}
    (hLY : L ≤ Y) (hL : IsPComponent 2 (L.subgroupOf Y)) (hs : IsSimpleGroup (OddBar L))
    (N : Subgroup ↥L) [N.Normal] (hN : N.index < Nat.card (OddBar L)) : N = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hres : CatalogueBPrimeJoin.primeResidual 2 ↥L = ⊤ :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L Y hLY).1 hL).2.1
  set O := pPrimeCore 2 ↥L with hO
  have : (N.map (QuotientGroup.mk' O)).Normal :=
    Subgroup.Normal.map inferInstance _ (QuotientGroup.mk'_surjective O)
  rcases hs.eq_bot_or_eq_top_of_normal (N.map (QuotientGroup.mk' O)) with hM | hM
  · exfalso
    have hNO : N ≤ O := by
      have := (Subgroup.map_eq_bot_iff _).mp hM
      rwa [QuotientGroup.ker_mk'] at this
    have hdvd : O.index ∣ N.index := Subgroup.index_dvd_of_le hNO
    have hNi : N.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hNi) hdvd
    have hOi : O.index = Nat.card (OddBar L) := rfl
    omega
  · apply top_unique
    rw [← hres]
    apply CatalogueBPrimeJoin.primeResidual_le_normal_of_coprime_index 2 N
    have hsup : O ⊔ N = ⊤ := by
      have := congrArg (Subgroup.comap (QuotientGroup.mk' O)) hM
      rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at this
      rwa [sup_comm] at this
    have hidx : N.index = N.relIndex O := by
      rw [← Subgroup.relIndex_top_right, ← hsup, Subgroup.relIndex_sup_right]
    rw [hidx]
    exact Nat.Coprime.coprime_dvd_right (Subgroup.relIndex_dvd_card N O)
      (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥L))

theorem mem_oddCoreIn_of_mem_inf {G : Type*} [Group G] [Finite G] {L J : Subgroup G}
    (hLN : L ≤ normalizer (J : Set G)) {c : G} (hcL : c ∈ L)
    (hcJ : c ∈ (pPrimeCore 2 ↥J).map J.subtype) : c ∈ (pPrimeCore 2 ↥L).map L.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O' : Subgroup G := (pPrimeCore 2 ↥J).map J.subtype with hO'
  set X : Subgroup ↥L := O'.subgroupOf L with hX
  have hXn : X.Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [hX, mem_subgroupOf] at hn ⊢
    have hgO : (g : G) ∈ normalizer (O' : Set G) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic J (pPrimeCore 2 ↥J) (hLN g.2)
    simpa using (mem_normalizer_iff.mp hgO _).mp hn
  have hXodd : Nat.Coprime 2 (Nat.card X) := by
    have h1 : Nat.card X = Nat.card ↥(O' ⊓ L) := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective, hX, subgroupOf_map_subtype]
    have h2 : Nat.card ↥(O' ⊓ L) ∣ Nat.card O' := Subgroup.card_dvd_of_le inf_le_left
    have h3 : Nat.card O' = Nat.card (pPrimeCore 2 ↥J) :=
      Subgroup.card_map_of_injective J.subtype_injective
    rw [h1]
    exact Nat.Coprime.coprime_dvd_right (h3 ▸ h2) (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥J))
  have hXO := LocalAnalysis.ComponentInitial.le_pPrimeCore hXn hXodd
  exact ⟨⟨c, hcL⟩, hXO (by rw [hX, mem_subgroupOf]; exact hcJ), rfl⟩

theorem conj_mem_normalizer_of_mem_normalizer_conjugate {G : Type*} [Group G] {X : Subgroup G}
    {w d : G} (hd : d ∈ normalizer (conjugate X w : Set G)) :
    w * d * w⁻¹ ∈ normalizer (X : Set G) := by
  rw [mem_normalizer_iff]
  intro b
  have h1 := mem_normalizer_iff.mp hd (w⁻¹ * b * w)
  rw [mem_conjugate_iff, mem_conjugate_iff, show w * (w⁻¹ * b * w) * w⁻¹ = b by group,
    show w * (d * (w⁻¹ * b * w) * d⁻¹) * w⁻¹ = w * d * w⁻¹ * b * (w * d * w⁻¹)⁻¹ by group] at h1
  exact h1

theorem conj_mem_normalizer_conjugate {G : Type*} [Group G] {X : Subgroup G} {e : G}
    (he : e ∈ normalizer (X : Set G)) (w : G) :
    w⁻¹ * e * w ∈ normalizer (conjugate X w : Set G) := by
  rw [mem_normalizer_iff]
  intro b
  rw [mem_conjugate_iff, mem_conjugate_iff,
    show w * (w⁻¹ * e * w * b * (w⁻¹ * e * w)⁻¹) * w⁻¹ = e * (w * b * w⁻¹) * e⁻¹ by group]
  exact mem_normalizer_iff.mp he (w * b * w⁻¹)

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem S_le_normalizer_D : h.S ≤ normalizer (h.D : Set H) := by
  intro s hs
  have hsJ : s ∈ normalizer (h.J : Set H) := (mem_inf.mp (h.S_le hs)).2
  apply mem_normalizer_of_conj_mem
  · intro y hy
    exact mem_inf.mpr ⟨mul_mem (mul_mem hs (mem_inf.mp hy).1) (inv_mem hs),
      (mem_normalizer_iff.mp hsJ y).mp (mem_inf.mp hy).2⟩
  · intro y hy
    have h1 := (mem_normalizer_iff.mp (inv_mem hsJ) y).mp (mem_inf.mp hy).2
    rw [inv_inv] at h1
    exact mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hs) (mem_inf.mp hy).1) hs, h1⟩

theorem eight_le_card_D (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c)
    (hCFc : CFProp23Center) (eJ : OddBar h.J ≃* alternatingGroup (Fin 6)) :
    8 ≤ Nat.card h.D := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set C := centralizer ({h.a} : Set H) with hC
  obtain ⟨-, R, hR⟩ := h.S_sylow_centralizer hB1 sylowKernelStatement hCF23 hCF24 hCFc
  have hCJ := h.centralizer_le_normalizer_J hB1 sylowKernelStatement hCF23 hCF24 hCFc
  have hJn : (h.J.subgroupOf C).Normal := (normal_subgroupOf_iff_le_normalizer h.J_le).mpr hCJ
  obtain ⟨P, hP⟩ := Glauberman.sylow_inf_normal R (N := h.J.subgroupOf C)
  have hSC : h.S ≤ C := h.S_le.trans inf_le_left
  have hPD : Nat.card (P : Subgroup ↥(h.J.subgroupOf C)) = Nat.card h.D := by
    rw [hP, hR]
    have hle : (h.S.subgroupOf C ⊓ h.J.subgroupOf C) ≤ h.J.subgroupOf C := inf_le_right
    rw [Nat.card_congr (subgroupOfEquivOfLe hle).toEquiv,
      ← Subgroup.card_map_of_injective C.subtype_injective,
      Subgroup.map_inf _ _ _ C.subtype_injective, subgroupOf_map_subtype, subgroupOf_map_subtype,
      inf_of_le_left hSC, inf_of_le_left h.J_le]
  have hJ8 : 8 ∣ Nat.card ↥(h.J.subgroupOf C) := by
    rw [Nat.card_congr (subgroupOfEquivOfLe h.J_le).toEquiv]
    have h1 : Nat.card (OddBar h.J) ∣ Nat.card h.J := Subgroup.card_quotient_dvd_card _
    have h2 : Nat.card (OddBar h.J) = 360 := by
      rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    rw [h2] at h1
    exact (show 8 ∣ 360 by norm_num).trans h1
  have hind : ¬ 2 ∣ (P : Subgroup ↥(h.J.subgroupOf C)).index := P.not_dvd_index
  have hmul := (P : Subgroup ↥(h.J.subgroupOf C)).card_mul_index
  have hcop : Nat.Coprime (2 ^ 3) (P : Subgroup ↥(h.J.subgroupOf C)).index :=
    Nat.Coprime.pow_left 3 ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hind)
  have h8 : 8 ∣ Nat.card (P : Subgroup ↥(h.J.subgroupOf C)) := by
    rw [← hmul] at hJ8
    exact hcop.dvd_of_dvd_mul_right hJ8
  rw [← hPD]
  exact Nat.le_of_dvd Nat.card_pos h8

theorem not_fused_of_row515 (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion)
    (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hrow : h.Row515)
    (hBab : ∀ u ∈ h.B, ∀ v ∈ h.B, u * v = v * u) (hB4 : Nat.card h.B ≤ 4) (g : H) :
    g * h.a * g⁻¹ ∉ h.B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hgB
  obtain ⟨⟨eJ⟩, hKa, ⟨eK⟩⟩ := hrow
  set C := centralizer ({h.a} : Set H) with hC
  have hSyl := (h.S_sylow_centralizer hB1 sylowKernelStatement hCF23 hCF24 hCFc).2
  have hCJ := h.centralizer_le_normalizer_J hB1 sylowKernelStatement hCF23 hCF24 hCFc
  have hKB : ∀ {k : H}, k ∈ h.K → ∀ {b : H}, b ∈ h.B → k * b = b * k := fun hk b hb =>
    (mem_centralizer_iff.mp ((h.K_le_layer_W.trans h.V_le_centralizer_B) hk) b hb).symm
  set B' := conjugate h.B g with hB'
  have haB' : h.a ∈ B' := by rw [hB', mem_conjugate_iff]; exact hgB
  have hB'C : B' ≤ C := by
    intro u hu
    rw [hB', mem_conjugate_iff] at hu
    have h1 := hBab _ hu _ hgB
    rw [mem_centralizer_singleton_iff]
    have h2 : g * (u * h.a) * g⁻¹ = g * (h.a * u) * g⁻¹ := by
      calc g * (u * h.a) * g⁻¹ = (g * u * g⁻¹) * (g * h.a * g⁻¹) := by group
        _ = (g * h.a * g⁻¹) * (g * u * g⁻¹) := h1
        _ = g * (h.a * u) * g⁻¹ := by group
    simpa using h2
  have hB'p : IsPGroup 2 B' := h.isPGroup_B.map (MulAut.conj g⁻¹).toMonoidHom
  obtain ⟨m, hmC, hmS⟩ := exists_conjugate_le_of_sylow hSyl hB'C hB'p
  set w := g * m with hw
  set B₁ := conjugate h.B w with hB₁
  have hB₁eq : conjugate B' m = B₁ := by rw [hB', hB₁, conjugate_conjugate]
  have hB₁S : B₁ ≤ h.S := by rw [← hB₁eq]; exact hmS
  have hma : m * h.a = h.a * m := mem_centralizer_singleton_iff.mp hmC
  have haB₁ : h.a ∈ B₁ := by
    rw [← hB₁eq, mem_conjugate_iff, hma, mul_inv_cancel_right]
    exact haB'
  have haw : w * h.a * w⁻¹ ∈ h.B := by
    rw [hB₁, mem_conjugate_iff] at haB₁
    exact haB₁
  set K₁ := conjugate h.K w with hK₁
  have hK₁C : ∀ {k : H}, k ∈ K₁ → k ∈ C := by
    intro k hk
    rw [hK₁, mem_conjugate_iff] at hk
    have h1 := hKB hk haw
    rw [mem_centralizer_singleton_iff]
    have h2 : w * (k * h.a) * w⁻¹ = w * (h.a * k) * w⁻¹ := by
      calc w * (k * h.a) * w⁻¹ = (w * k * w⁻¹) * (w * h.a * w⁻¹) := by group
        _ = (w * h.a * w⁻¹) * (w * k * w⁻¹) := h1
        _ = w * (h.a * k) * w⁻¹ := by group
    simpa using h2
  have hKperf : Group.IsPerfect ↥h.K := by
    have := CatalogueBHeldSmallCore.pComponent_perfect 2 _ h.isPComponent_K.2
    exact Group.IsPerfect.ofSurjective (f := (subgroupOfEquivOfLe h.isPComponent_K.1).toMonoidHom)
      (subgroupOfEquivOfLe h.isPComponent_K.1).surjective
  have : Group.IsSolvable (OuterAutomorphisms.Outer (OddBar h.J)) :=
    CatalogueSchreierAlternating.alternating_schreier_of_equiv 6 (by norm_num) eJ
  have hsK : IsSimpleGroup (OddBar h.K) := by
    have : IsSimpleGroup (alternatingGroup (Fin 10)) := alternatingGroup.isSimpleGroup (by simp)
    exact (MulEquiv.isSimpleGroup_congr eK).mpr this
  have hcJ : Nat.card (OddBar h.J) = 360 := by
    rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hcK : Nat.card (OddBar h.K) = 1814400 := by
    rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
    decide
  have hA : ∀ N : Subgroup ↥h.K, N.Normal → N.index ≤ Nat.card (OddBar h.J) → N = ⊤ := by
    intro N hN hle
    exact eq_top_of_index_lt_of_pComponent h.isPComponent_K.1 h.isPComponent_K.2 hsK N
      (by rw [hcK]; rw [hcJ] at hle; omega)
  have hfmem : ∀ k : ↥h.K, (MulAut.conj w⁻¹).toMonoidHom.comp h.K.subtype k ∈
      normalizer (h.J : Set H) := fun k => hCJ (hK₁C ⟨k, k.2, rfl⟩)
  set f : ↥h.K →* ↥(normalizer (h.J : Set H)) :=
    ((MulAut.conj w⁻¹).toMonoidHom.comp h.K.subtype).codRestrict _ hfmem with hf
  have hK₁CK : ∀ {k : H}, k ∈ K₁ → k ∈ coreActionKernel h.J := by
    intro k hk
    have hk' : w * k * w⁻¹ ∈ h.K := by rw [hK₁, mem_conjugate_iff] at hk; exact hk
    have h1 := mem_coreActionKernel_of_perfect_of_index f hA ⟨_, hk'⟩
    have hval : ((f ⟨_, hk'⟩ : ↥(normalizer (h.J : Set H))) : H) = k := by
      simp only [hf, MonoidHom.codRestrict_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
        MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
      group
    rwa [hval] at h1
  have hDB : h.D ≤ B₁ := by
    by_contra hDB
    set R₀ := h.D ⊔ B₁ with hR₀
    have hR₀S : R₀ ≤ h.S := sup_le h.D_le_S hB₁S
    have hR₀p : IsPGroup 2 R₀ := h.isPGroup_S.to_le hR₀S
    have : Group.IsNilpotent ↥R₀ := hR₀p.isNilpotent
    have hlt : B₁.subgroupOf R₀ < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro htop
      apply hDB
      intro d hd
      have : (⟨d, mem_sup_left hd⟩ : ↥R₀) ∈ B₁.subgroupOf R₀ := htop ▸ mem_top _
      exact mem_subgroupOf.mp this
    obtain ⟨r, hrN, hrB⟩ :=
      IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
    have hrN' : (r : H) ∈ normalizer (B₁ : Set H) := by
      apply mem_normalizer_of_conj_mem
      · intro b hb
        have h1 := (mem_normalizer_iff.mp hrN ⟨b, mem_sup_right hb⟩).mp (mem_subgroupOf.mpr hb)
        rw [mem_subgroupOf] at h1
        simpa using h1
      · intro b hb
        have h1 := (mem_normalizer_iff.mp (inv_mem hrN) ⟨b, mem_sup_right hb⟩).mp
          (mem_subgroupOf.mpr hb)
        rw [mem_subgroupOf] at h1
        simpa using h1
    have hB₁D : B₁ ≤ normalizer (h.D : Set H) := hB₁S.trans h.S_le_normalizer_D
    have hrm : (r : H) ∈ (h.D : Set H) * (B₁ : Set H) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hB₁D]
      exact r.2
    obtain ⟨d, hd, β, hβ, hdβ⟩ := Set.mem_mul.mp hrm
    have hdeq : d = (r : H) * β⁻¹ := by rw [← hdβ]; group
    have hdN : d ∈ normalizer (B₁ : Set H) := by
      rw [hdeq]
      exact mul_mem hrN' (inv_mem (le_normalizer hβ))
    have hdB : d ∉ B₁ := by
      intro hdB
      apply hrB
      rw [mem_subgroupOf, ← hdβ]
      exact mul_mem hdB hβ
    set e := w * d * w⁻¹ with he
    have heW : e ∈ h.W := conj_mem_normalizer_of_mem_normalizer_conjugate hdN
    have heK : e ∈ normalizer (h.K : Set H) := by
      have := mem_normalizer_layerIn heW
      rwa [show layerIn h.W = h.K from h.V_eq_K hKa] at this
    have hdK₁ : d ∈ normalizer (K₁ : Set H) := by
      have := conj_mem_normalizer_conjugate heK w
      rwa [show w⁻¹ * e * w = d by rw [he]; group] at this
    have hdCK : d ∈ coreActionKernel K₁ := by
      refine mem_coreActionKernel.mpr ⟨hdK₁, fun k hk => ?_⟩
      have h1 := (mem_coreActionKernel.mp (hK₁CK hk)).2 d (h.D_le_J hd)
      have h2 : k⁻¹ * d⁻¹ * k * d ∈ (pPrimeCore 2 ↥h.J).map h.J.subtype := by
        have := inv_mem h1
        rwa [show (d⁻¹ * k⁻¹ * d * k)⁻¹ = k⁻¹ * d⁻¹ * k * d by group] at this
      have h3 : k⁻¹ * d⁻¹ * k * d ∈ K₁ := by
        have h4 : d⁻¹ * k * d ∈ K₁ := by
          have := (mem_normalizer_iff.mp (inv_mem hdK₁) k).mp hk
          rwa [inv_inv] at this
        rw [show k⁻¹ * d⁻¹ * k * d = k⁻¹ * (d⁻¹ * k * d) by group]
        exact mul_mem (inv_mem hk) h4
      exact mem_oddCoreIn_of_mem_inf (fun y hy => hCJ (hK₁C hy)) h3 h2
    have heCK : e ∈ coreActionKernel h.K := by
      have := GSLit.conj_mem_coreActionKernel_conjugate hdCK w⁻¹
      rwa [inv_inv, hK₁, conjugate_conjugate_inv] at this
    obtain ⟨k₀, hk₀⟩ := h.orderOf_eq_two_pow_of_mem_S (h.D_le_S hd)
    have hek : e ^ 2 ^ k₀ = 1 := by
      rw [he, conj_pow, ← hk₀, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    have hBS := h.B_sylow_kernel
    rw [show layerIn (normalizer (h.B : Set H)) = h.K from h.V_eq_K hKa] at hBS
    have heB : e ∈ h.B :=
      mem_of_sylow_of_le_normalizer inf_le_left hBS (mem_inf.mpr ⟨heW, heCK⟩) hek
    apply hdB
    rw [hB₁, mem_conjugate_iff]
    exact heB
  have h1 : Nat.card h.D ≤ Nat.card B₁ := Subgroup.card_le_of_le hDB
  have h2 : Nat.card B₁ = Nat.card h.B := card_map_of_injective (MulAut.conj w⁻¹).injective
  have h8 := h.eight_le_card_D hB1 hCF23 hCF24 hCFc eJ
  omega

end Hyp52

namespace Hyp59

variable {H : Type} [Group H] [Finite H] (h : Hyp59 H)

theorem B_comm_card_le_four (hP21 : CFProp21A10) (hrow : h.Row515) :
    (∀ u ∈ h.B, ∀ v ∈ h.B, u * v = v * u) ∧ Nat.card h.B ≤ 4 := by
  obtain ⟨hTB4, hTB2⟩ := hP21 H h.toHyp52 hrow
  set B' := conjugate h.B h.x with hB'def
  have hxT := h.x_mem_normalizer_T
  have hconjT : ∀ {y : H}, y ∈ h.T → h.x * y * h.x⁻¹ ∈ h.T := fun hy =>
    (mem_normalizer_iff.mp hxT _).mp hy
  have hT2 : ∀ t ∈ h.T, t ^ 2 = 1 := by
    intro t ht
    have h1 := hTB2 t ht
    have h2 : t ^ 2 ∈ B' := by
      rw [hB'def, mem_conjugate_iff, ← conj_pow]
      exact hTB2 _ (hconjT ht)
    have := h.inf_conjugate_x ▸ mem_inf.mpr ⟨h1, h2⟩
    exact mem_bot.mp this
  refine ⟨fun u hu v hv => ?_, ?_⟩
  · have hBT := h.toHyp52.B_le_T
    have h1 := hT2 _ (mul_mem (hBT hu) (hBT hv))
    have hu1 := hT2 u (hBT hu)
    have hv1 := hT2 v (hBT hv)
    rw [pow_two] at h1 hu1 hv1
    calc u * v = (u * v)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
      _ = v⁻¹ * u⁻¹ := mul_inv_rev u v
      _ = v * u := by rw [inv_eq_of_mul_eq_one_right hu1, inv_eq_of_mul_eq_one_right hv1]
  · obtain ⟨f, hf⟩ := h.embeds_T_quot
    exact hTB4 ▸ Nat.card_le_card_of_injective f hf

theorem not_fused_of_row515 (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion)
    (hCF24 : CFProp24c) (hCFc : CFProp23Center) (hP21 : CFProp21A10) (hrow : h.Row515) (g : H) :
    g * h.a * g⁻¹ ∉ h.B := by
  obtain ⟨hBab, hB4⟩ := h.B_comm_card_le_four hP21 hrow
  exact h.toHyp52.not_fused_of_row515 hB1 hCF23 hCF24 hCFc hrow hBab hB4 g

end Hyp59

end CFSG.ComponentClassification.GSThmB
