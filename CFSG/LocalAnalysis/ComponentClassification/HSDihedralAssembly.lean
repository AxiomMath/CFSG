module

public import CFSG.LocalAnalysis.ComponentClassification.HSDihedralSetup
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsTransport
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSqClass
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG

public noncomputable section

namespace CFSG.ComponentClassification.HSDihedral

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools
open CFSG.ComponentClassification.HarrisLit
open scoped commutatorElement

variable {X : Type} [Group X] {t : X} {L : Subgroup X} {p f : ℕ}

@[expose] def CoreAt (t : X) (L S : Subgroup X) : Prop :=
  S ⊓ coreActionKernel L = zpowers t ∧ (∃ s ∈ S, orderOf s = 2 ∧ ActsAsFieldAut L s) ∧
    ∀ p f : ℕ, p.Prime → p ≠ 2 → Blueprint.LieModel (Bar L) .PSL 2 p f → Even f

section Burnside

variable {G : Type*} [Group G] [Finite G]

theorem exists_odd_normal_complement (P : Sylow 2 G) (hP : Nat.card (P : Subgroup G) = 2) :
    ∃ K : Subgroup G, K.Normal ∧ ¬ 2 ∣ Nat.card K ∧
      (∀ g : G, Nat.Coprime (orderOf g) 2 → g ∈ K) ∧ Nat.card K * 2 = Nat.card G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : normalizer ((P : Subgroup G) : Set G) ≤ centralizer ((P : Subgroup G) : Set G) := by
    intro g hg
    rw [mem_centralizer_iff]
    intro x hx
    have hxg : g * x * g⁻¹ ∈ (P : Subgroup G) := (mem_normalizer_iff.mp hg x).mp hx
    by_cases hx1 : x = 1
    · rw [hx1, mul_one, one_mul]
    have hcard : ∀ a ∈ (P : Subgroup G), a ≠ 1 → a = x := by
      intro a ha ha1
      obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : (P : Subgroup G))).mp hP
      have h1 := hy ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
      have h2 := hy ⟨x, hx⟩ (fun h => hx1 (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
    have hgx1 : g * x * g⁻¹ ≠ 1 := by
      intro h1
      apply hx1
      have : x = g⁻¹ * (g * x * g⁻¹) * g := by group
      rw [this, h1]; group
    have := hcard _ hxg hgx1
    calc x * g = g * x * g⁻¹ * g := by rw [this]
      _ = g * x := by group
  refine ⟨(MonoidHom.transferSylow P hle).ker, inferInstance,
    MonoidHom.not_dvd_card_ker_transferSylow P hle, ?_, ?_⟩
  · intro g hg
    rw [MonoidHom.mem_ker]
    obtain ⟨k, hk⟩ := P.isPGroup' (MonoidHom.transferSylow P hle g)
    have h1 := orderOf_dvd_of_pow_eq_one hk
    have h2 := orderOf_map_dvd (MonoidHom.transferSylow P hle) g
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes (hg.pow_right k) h2 h1)
  · have h := (MonoidHom.ker_transferSylow_isComplement' P hle).card_mul_card
    rw [hP] at h
    exact h

end Burnside

section Kernel

variable [Finite X]

theorem le_pPrimeCore_of_normal {G : Type*} [Group G] {K : Subgroup G} (hK : K.Normal)
    (hc : Nat.Coprime 2 (Nat.card K)) : K ≤ pPrimeCore 2 G :=
  le_sSup (s := {K : Subgroup G | K.Normal ∧ Nat.Coprime 2 (Nat.card K)}) ⟨hK, hc⟩

theorem eq_of_card_le_two {E : Subgroup X} (hE : Nat.card E ≤ 2) {a b : X} (ha : a ∈ E)
    (hb : b ∈ E) (ha1 : a ≠ 1) (hb1 : b ≠ 1) : a = b := by
  have hne : E ≠ ⊥ := fun h => ha1 (by rw [h] at ha; exact (mem_bot.mp ha))
  have h2 : Nat.card E = 2 := by
    have := (Subgroup.one_lt_card_iff_ne_bot E).mpr hne
    omega
  obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : E)).mp h2
  have h1 := hy ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
  have h1' := hy ⟨b, hb⟩ (fun h => hb1 (congrArg Subtype.val h))
  exact congrArg Subtype.val (h1.trans h1'.symm)

theorem card_of_isSylowOf_kernel (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (hc : S ⊓ coreActionKernel L = zpowers t)
    {P : Subgroup X} (hP : IsSylowOf 2 P (centralizer ({t} : Set X) ⊓ coreActionKernel L)) :
    Nat.card P = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [hP.card_eq, ← (isSylowOf_inf_kernel h hS).card_eq, hc, Nat.card_zpowers, h.orderOf_eq]

theorem card_le_two_of_le_kernel (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (hc : S ⊓ coreActionKernel L = zpowers t)
    {E : Subgroup X} (hE : IsPGroup 2 E)
    (hEK : E ≤ centralizer ({t} : Set X) ⊓ coreActionKernel L) : Nat.card E ≤ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := centralizer ({t} : Set X) ⊓ coreActionKernel L
  have hE' : IsPGroup 2 (E.subgroupOf K) := hE.comap_of_injective K.subtype (subtype_injective _)
  obtain ⟨P, hP⟩ := hE'.exists_le_sylow
  have hPc := card_of_isSylowOf_kernel h hS hc (P := (P : Subgroup K).map K.subtype) ⟨P, rfl⟩
  rw [card_map_of_injective K.subtype_injective] at hPc
  calc Nat.card E = Nat.card (E.subgroupOf K) :=
        (Nat.card_congr (subgroupOfEquivOfLe hEK).toEquiv).symm
    _ ≤ Nat.card (P : Subgroup K) := Subgroup.card_le_of_le hP
    _ = 2 := hPc

theorem card_sylow_coreActionKernel (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (hc : S ⊓ coreActionKernel L = zpowers t)
    (P : Sylow 2 ↥(coreActionKernel L)) :
    Nat.card (P : Subgroup ↥(coreActionKernel L)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have htK : t ∈ coreActionKernel L := t_mem_kernel h
  have ht1 : t ≠ 1 := by
    intro h1
    have := h.orderOf_eq
    rw [h1, orderOf_one] at this
    norm_num at this
  have ht2 : IsPGroup 2 ((zpowers t).subgroupOf (coreActionKernel L)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_congr (subgroupOfEquivOfLe ((zpowers_le).mpr htK)).toEquiv, Nat.card_zpowers,
      h.orderOf_eq, pow_one]
  obtain ⟨P₁, hP₁⟩ := ht2.exists_le_sylow
  rw [Sylow.card_eq_multiplicity P, ← Sylow.card_eq_multiplicity P₁]
  set A := (P₁ : Subgroup ↥(coreActionKernel L)).map (coreActionKernel L).subtype with hA
  have htA : t ∈ A := ⟨⟨t, htK⟩, hP₁ (mem_subgroupOf.mpr (mem_zpowers t)), rfl⟩
  have hA2 : IsPGroup 2 A := P₁.isPGroup'.map _
  have hAK : A ≤ coreActionKernel L := map_subtype_le _
  have hcent : ∀ a ∈ A, a * t = t * a := by
    have hA2' : IsPGroup 2 ↥A := hA2
    have : Nontrivial ↥A := ⟨⟨⟨t, htA⟩, 1, fun h' => ht1 (congrArg Subtype.val h')⟩⟩
    have := hA2'.center_nontrivial
    have h2Z : 2 ∣ Nat.card ↥(center ↥A) := by
      obtain ⟨n, hn⟩ := (hA2'.to_subgroup (center ↥A)).exists_card_eq
      have hn0 : n ≠ 0 := by
        rintro rfl
        rw [pow_zero] at hn
        exact (Finite.one_lt_card (α := ↥(center ↥A))).ne' hn
      rw [hn]
      exact dvd_pow_self 2 hn0
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2Z
    have hu1 : ((u : ↥A) : X) ≠ 1 := by
      intro h1
      have : u = 1 := by
        apply Subtype.ext
        exact Subtype.ext h1
      rw [this, orderOf_one] at hu
      norm_num at hu
    have hut : ((u : ↥A) : X) * t = t * ((u : ↥A) : X) := by
      have := (Subgroup.mem_center_iff.mp u.2 (⟨t, htA⟩ : ↥A))
      exact (congrArg Subtype.val this).symm
    have huH : ((u : ↥A) : X) ∈ centralizer ({t} : Set X) :=
      mem_centralizer_singleton_iff.mpr hut
    set E := A ⊓ centralizer ({t} : Set X)
    have hE2 : IsPGroup 2 E := hA2.to_le inf_le_left
    have hEle : Nat.card E ≤ 2 :=
      card_le_two_of_le_kernel h hS hc hE2 (le_inf inf_le_right (inf_le_left.trans hAK))
    have htE : t ∈ E := ⟨htA, mem_centralizer_singleton_iff.mpr rfl⟩
    have huE : ((u : ↥A) : X) ∈ E := ⟨(u : ↥A).2, huH⟩
    have hut' : ((u : ↥A) : X) = t := eq_of_card_le_two hEle huE htE hu1 ht1
    intro a ha
    have := (Subgroup.mem_center_iff.mp u.2 (⟨a, ha⟩ : ↥A))
    rw [← hut']
    exact congrArg Subtype.val this
  have hAH : A ≤ centralizer ({t} : Set X) := fun a ha =>
    mem_centralizer_singleton_iff.mpr (hcent a ha)
  have hAle : Nat.card A ≤ 2 := card_le_two_of_le_kernel h hS hc hA2 (le_inf hAH hAK)
  have hA1 : 2 ≤ Nat.card A := by
    have hne : A ≠ ⊥ := fun h' => ht1 (by rw [h'] at htA; exact mem_bot.mp htA)
    have := (Subgroup.one_lt_card_iff_ne_bot A).mpr hne
    omega
  have hAc : Nat.card A = Nat.card (P₁ : Subgroup ↥(coreActionKernel L)) :=
    card_map_of_injective (coreActionKernel L).subtype_injective
  omega

theorem pPrimeCore_le_kernel (h : Config t L p f) :
    (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype ≤
      coreActionKernel L := by
  set H := centralizer ({t} : Set X) with hH
  set O := (pPrimeCore 2 ↥H).map H.subtype with hO
  have hOnorm : ∀ a ∈ H, ∀ x ∈ O, a * x * a⁻¹ ∈ O := by
    rintro a ha _ ⟨x, hx, rfl⟩
    exact ⟨⟨a, ha⟩ * x * (⟨a, ha⟩)⁻¹, pPrimeCore_normal.conj_mem x hx ⟨a, ha⟩, rfl⟩
  have hOodd : Nat.Coprime 2 (Nat.card O) := by
    rw [hO, card_map_of_injective H.subtype_injective]
    exact pPrimeCore_coprime_card
  rintro _ ⟨g, hg, rfl⟩
  have hgO : (g : X) ∈ O := ⟨g, hg, rfl⟩
  rw [mem_coreActionKernel]
  refine ⟨le_normalizer h g.2, fun j hj => ?_⟩
  have hjH : j ∈ H := h.le_centralizer hj
  have hcO : j⁻¹ * (g : X)⁻¹ * j * g ∈ O := by
    have h1 := hOnorm j⁻¹ (inv_mem hjH) _ (inv_mem hgO)
    rw [inv_inv] at h1
    exact mul_mem h1 hgO
  have hcL : j⁻¹ * (g : X)⁻¹ * j * g ∈ L := by
    have h1 : (g : X)⁻¹ * j * g ∈ L := by
      have := (mem_normalizer_iff.mp (inv_mem (le_normalizer h g.2)) j).mp hj
      rwa [inv_inv] at this
    rw [show j⁻¹ * (g : X)⁻¹ * j * g = j⁻¹ * ((g : X)⁻¹ * j * g) by group]
    exact mul_mem (inv_mem hj) h1
  set N := (O ⊓ L).subgroupOf L with hN
  have hNnorm : N.Normal := by
    constructor
    intro n hn l
    rw [mem_subgroupOf] at hn ⊢
    refine ⟨hOnorm l (h.le_centralizer l.2) n hn.1, ?_⟩
    exact (l * n * l⁻¹).2
  have hNodd : Nat.Coprime 2 (Nat.card N) := by
    have hle : Nat.card N ∣ Nat.card O := by
      rw [show Nat.card N = Nat.card ↥(O ⊓ L) from
        Nat.card_congr (subgroupOfEquivOfLe inf_le_right).toEquiv]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact Nat.Coprime.coprime_dvd_right hle hOodd
  have hNle : N ≤ pPrimeCore 2 L := le_pPrimeCore_of_normal hNnorm hNodd
  have hmem : (⟨_, hcL⟩ : L) ∈ N := mem_subgroupOf.mpr ⟨hcO, hcL⟩
  exact ⟨_, hNle hmem, rfl⟩

theorem kernel_eq_of_core (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (hc : S ⊓ coreActionKernel L = zpowers t) :
    centralizer ({t} : Set X) ⊓ coreActionKernel L =
      (pPrimeCore 2 ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype ⊔
        zpowers t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := centralizer ({t} : Set X) with hH
  set K₀ := H ⊓ coreActionKernel L with hK₀
  set O := (pPrimeCore 2 ↥H).map H.subtype with hO
  have htH : t ∈ H := mem_centralizer_singleton_iff.mpr rfl
  have htK₀ : t ∈ K₀ := ⟨htH, t_mem_kernel h⟩
  apply le_antisymm
  · obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥K₀))
    have hP2 : Nat.card (P : Subgroup ↥K₀) = 2 := by
      have := card_of_isSylowOf_kernel h hS hc (P := (P : Subgroup ↥K₀).map K₀.subtype) ⟨P, rfl⟩
      rwa [card_map_of_injective K₀.subtype_injective] at this
    obtain ⟨N, hNn, hNodd, hNall, hNcard⟩ := exists_odd_normal_complement P hP2
    have hNodd' : Nat.Coprime 2 (Nat.card N) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hNodd
    have hcopN : ∀ m ∈ N, Nat.Coprime (orderOf m) 2 := fun m hm =>
      (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard N hm) hNodd').symm
    have hNO : ∀ m ∈ N, ((m : ↥K₀) : X) ∈ O := by
      set NH := (N.map K₀.subtype).subgroupOf H with hNH
      have hNHn : NH.Normal := by
        constructor
        intro y hy a
        rw [mem_subgroupOf] at hy ⊢
        obtain ⟨m, hm, hmy⟩ := hy
        have hK₀n := le_normalizer_kernel h a.2
        have hx : (a : X) * (y : X) * (a : X)⁻¹ ∈ K₀ := by
          rw [← hmy]
          exact (mem_normalizer_iff.mp hK₀n _).mp m.2
        refine ⟨⟨_, hx⟩, hNall _ ?_, rfl⟩
        have hord : orderOf (⟨_, hx⟩ : ↥K₀) = orderOf m := by
          rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe m]
          simp only
          have := MulEquiv.orderOf_eq (MulAut.conj (a : X)) ((m : ↥K₀) : X)
          rw [MulAut.conj_apply] at this
          rw [← hmy]
          exact this
        rw [hord]
        exact hcopN m hm
      have hNHc : Nat.Coprime 2 (Nat.card NH) := by
        have : Nat.card NH = Nat.card N := by
          rw [show Nat.card NH = Nat.card ↥(N.map K₀.subtype) from
            Nat.card_congr (subgroupOfEquivOfLe (map_subtype_le N |>.trans inf_le_left)).toEquiv,
            card_map_of_injective K₀.subtype_injective]
        rw [this]
        exact hNodd'
      have hle := le_pPrimeCore_of_normal hNHn hNHc
      intro m hm
      have hmH : ((m : ↥K₀) : X) ∈ H := (m : ↥K₀).2.1
      have : (⟨_, hmH⟩ : ↥H) ∈ NH := mem_subgroupOf.mpr ⟨m, hm, rfl⟩
      exact ⟨_, hle this, rfl⟩
    intro k hk
    have hQ : Nat.card (↥K₀ ⧸ N) = 2 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
      rw [← hNcard] at h1
      have hpos : 0 < Nat.card N := Nat.card_pos
      have : Nat.card (↥K₀ ⧸ N) * Nat.card N = 2 * Nat.card N := by rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_right hpos this
    have htN : (⟨t, htK₀⟩ : ↥K₀) ∉ N := by
      intro htN
      have := hcopN _ htN
      rw [Subgroup.orderOf_mk, h.orderOf_eq] at this
      norm_num at this
    by_cases hkN : (⟨k, hk⟩ : ↥K₀) ∈ N
    · exact mem_sup_left (hNO _ hkN)
    · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥K₀ ⧸ N)).mp hQ
      have h1 := hy (QuotientGroup.mk (⟨k, hk⟩ : ↥K₀))
        (fun h' => hkN ((QuotientGroup.eq_one_iff _).mp h'))
      have h2 := hy (QuotientGroup.mk (⟨t, htK₀⟩ : ↥K₀))
        (fun h' => htN ((QuotientGroup.eq_one_iff _).mp h'))
      have h3 := QuotientGroup.eq.mp (h2.trans h1.symm)
      have h4 := hNO _ h3
      have : k = t * ((⟨t, htK₀⟩ : ↥K₀)⁻¹ * ⟨k, hk⟩ : ↥K₀) := by
        simp
      rw [this]
      exact mul_mem (mem_sup_right (mem_zpowers t)) (mem_sup_left h4)
  · exact sup_le (le_inf (map_subtype_le _) (pPrimeCore_le_kernel h)) ((zpowers_le).mpr htK₀)

theorem eq_one_or_eq_of_mem_zpowers {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1)
    (hb : b ∈ zpowers a) : b = 1 ∨ b = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hb
  rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
  · left
    rw [zpow_mul, show a ^ (2 : ℤ) = 1 by exact_mod_cast ha, one_zpow]
  · right
    rw [zpow_add, zpow_mul, show a ^ (2 : ℤ) = 1 by exact_mod_cast ha, one_zpow, one_mul,
      zpow_one]

theorem normalizer_eq_of_core (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (hc : S ⊓ coreActionKernel L = zpowers t) :
    normalizer (L : Set X) =
      (pPrimeCore 2 ↥(normalizer (L : Set X))).map (normalizer (L : Set X)).subtype ⊔
        centralizer ({t} : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := normalizer (L : Set X) with hN
  set C := coreActionKernel L with hC
  set O := (pPrimeCore 2 ↥N).map N.subtype with hO
  have htC : t ∈ C := t_mem_kernel h
  have ht2 : t ^ 2 = 1 := by rw [← h.orderOf_eq, pow_orderOf_eq_one]
  have hCN : C ≤ N := fun x hx => (mem_coreActionKernel.mp hx).1
  have hCnorm : ∀ g ∈ N, ∀ c ∈ C, g * c * g⁻¹ ∈ C := by
    intro g hg c hcC
    have h1 : (⟨c, hCN hcC⟩ : ↥N) ∈ (barAction L).ker := (mem_ker_barAction L _).mpr hcC
    have h2 := (barAction L).normal_ker.conj_mem _ h1 ⟨g, hg⟩
    exact (mem_ker_barAction L _).mp h2
  apply le_antisymm
  · intro g hg
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥C))
    have hP2 := card_sylow_coreActionKernel h hS hc P
    obtain ⟨K, hKn, hKodd, hKall, hKcard⟩ := exists_odd_normal_complement P hP2
    have hKodd' : Nat.Coprime 2 (Nat.card K) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hKodd
    have hcopK : ∀ m ∈ K, Nat.Coprime (orderOf m) 2 := fun m hm =>
      (Nat.Coprime.coprime_dvd_right (Subgroup.orderOf_dvd_natCard K hm) hKodd').symm
    have hKO : ∀ m ∈ K, ((m : ↥C) : X) ∈ O := by
      set KN := (K.map C.subtype).subgroupOf N with hKN
      have hKNn : KN.Normal := by
        constructor
        intro y hy a
        rw [mem_subgroupOf] at hy ⊢
        obtain ⟨m, hm, hmy⟩ := hy
        have hx : (a : X) * (y : X) * (a : X)⁻¹ ∈ C := by
          rw [← hmy]
          exact hCnorm _ a.2 _ m.2
        refine ⟨⟨_, hx⟩, hKall _ ?_, rfl⟩
        have hord : orderOf (⟨_, hx⟩ : ↥C) = orderOf m := by
          rw [← Subgroup.orderOf_coe, ← Subgroup.orderOf_coe m]
          simp only
          have := MulEquiv.orderOf_eq (MulAut.conj (a : X)) ((m : ↥C) : X)
          rw [MulAut.conj_apply] at this
          rw [← hmy]
          exact this
        rw [hord]
        exact hcopK m hm
      have hKNc : Nat.Coprime 2 (Nat.card KN) := by
        have : Nat.card KN = Nat.card K := by
          rw [show Nat.card KN = Nat.card ↥(K.map C.subtype) from
            Nat.card_congr (subgroupOfEquivOfLe ((map_subtype_le K).trans hCN)).toEquiv,
            card_map_of_injective C.subtype_injective]
        rw [this]
        exact hKodd'
      have hle := le_pPrimeCore_of_normal hKNn hKNc
      intro m hm
      have : (⟨_, hCN (m : ↥C).2⟩ : ↥N) ∈ KN := mem_subgroupOf.mpr ⟨m, hm, rfl⟩
      exact ⟨_, hle this, rfl⟩
    have hgt : g * t * g⁻¹ ∈ C := hCnorm g hg t htC
    have hsyl : ∀ x ∈ C, orderOf x = 2 →
        Nat.card ↥((zpowers x).subgroupOf C) = 2 ^ (Nat.card ↥C).factorization 2 := by
      intro x hx hx2
      rw [Nat.card_congr (subgroupOfEquivOfLe ((zpowers_le).mpr hx)).toEquiv, Nat.card_zpowers,
        hx2, ← Sylow.card_eq_multiplicity P, hP2]
    have hgt2 : orderOf (g * t * g⁻¹) = 2 := by
      have := MulEquiv.orderOf_eq (MulAut.conj g) t
      rw [MulAut.conj_apply] at this
      rw [this, h.orderOf_eq]
    obtain ⟨c, hcQ⟩ := MulAction.exists_smul_eq ↥C
      (Sylow.ofCard _ (hsyl _ hgt hgt2)) (Sylow.ofCard _ (hsyl t htC h.orderOf_eq))
    have hmem : (c : X) * (g * t * g⁻¹) * (c : X)⁻¹ ∈ zpowers t := by
      have h1 : c * ⟨g * t * g⁻¹, hgt⟩ * c⁻¹ ∈
          ((Sylow.ofCard _ (hsyl t htC h.orderOf_eq) : Sylow 2 ↥C) : Subgroup ↥C) := by
        rw [← hcQ, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists]
        refine ⟨⟨g * t * g⁻¹, hgt⟩, ?_, ?_⟩
        · rw [Sylow.coe_ofCard, mem_subgroupOf]
          exact mem_zpowers _
        · rw [MulAut.smul_def, MulAut.conj_apply]
      rw [Sylow.coe_ofCard, mem_subgroupOf] at h1
      exact h1
    have hct : (c : X) * (g * t * g⁻¹) * (c : X)⁻¹ = t := by
      rcases eq_one_or_eq_of_mem_zpowers ht2 hmem with h1 | h1
      · exfalso
        have : t = 1 := by
          have h2 : t = (g⁻¹ * (c : X)⁻¹) * ((c : X) * (g * t * g⁻¹) * (c : X)⁻¹) *
              ((c : X) * g) := by group
          rw [h2, h1]
          group
        rw [this] at ht2
        have := h.orderOf_eq
        rw [‹t = 1›, orderOf_one] at this
        norm_num at this
      · exact h1
    have hcgH : (c : X) * g ∈ centralizer ({t} : Set X) := by
      rw [mem_centralizer_singleton_iff]
      calc (c : X) * g * t = (c : X) * (g * t * g⁻¹) * (c : X)⁻¹ * ((c : X) * g) := by group
        _ = t * ((c : X) * g) := by rw [hct]
    have hQ : Nat.card (↥C ⧸ K) = 2 := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup K
      rw [← hKcard] at h1
      have hpos : 0 < Nat.card K := Nat.card_pos
      have : Nat.card (↥C ⧸ K) * Nat.card K = 2 * Nat.card K := by rw [← h1]; ring
      exact Nat.eq_of_mul_eq_mul_right hpos this
    have htK : (⟨t, htC⟩ : ↥C) ∉ K := by
      intro htK
      have := hcopK _ htK
      rw [Subgroup.orderOf_mk, h.orderOf_eq] at this
      norm_num at this
    have hg' : g = ((c⁻¹ : ↥C) : X) * ((c : X) * g) := by
      simp
    rw [hg']
    by_cases hcK : c⁻¹ ∈ K
    · exact mul_mem (mem_sup_left (hKO _ hcK)) (mem_sup_right hcgH)
    · obtain ⟨y, -, hy⟩ := (Nat.card_eq_two_iff' (1 : ↥C ⧸ K)).mp hQ
      have h1 := hy (QuotientGroup.mk c⁻¹) (fun h' => hcK ((QuotientGroup.eq_one_iff _).mp h'))
      have h2 := hy (QuotientGroup.mk (⟨t, htC⟩ : ↥C))
        (fun h' => htK ((QuotientGroup.eq_one_iff _).mp h'))
      have h3 := QuotientGroup.eq.mp (h1.trans h2.symm)
      have h4 := hKO _ h3
      have htH : t ∈ centralizer ({t} : Set X) := mem_centralizer_singleton_iff.mpr rfl
      have h6 : ((c⁻¹ : ↥C) : X) * ((c : X) * g) =
          t * ((((c⁻¹)⁻¹ * ⟨t, htC⟩ : ↥C) : X)⁻¹ * ((c : X) * g)) := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_inv_rev]
        group
      rw [h6]
      exact mul_mem (mem_sup_right htH) (mul_mem (mem_sup_left (inv_mem h4)) (mem_sup_right hcgH))
  · exact sup_le (map_subtype_le _) (le_normalizer h)

end Kernel

section Residual

variable [Finite X]

private theorem innAut_normal_aux (Y : Type*) [Group Y] :
    (MulAut.conj : Y →* MulAut Y).range.Normal :=
  ⟨fun _ ⟨s, hs⟩ g => ⟨g s, by
    rw [← hs]
    ext y
    simp [MulAut.mul_apply, MulAut.conj_apply]⟩⟩

omit [Finite X] in
theorem commutator_mem_innAut (h : Config t L p f) (a b : MulAut (Bar L)) :
    ⁅a, b⁆ ∈ innAut (Bar L) := by
  obtain ⟨-, -, -, -, F, _, _, -, ⟨e⟩⟩ := AutL2Facts.lieModel_psl2_data h.lieModel
  have h1 := AutL2Facts.commutator_mem_pslRange (AutL2Facts.autEquiv e a) (AutL2Facts.autEquiv e b)
  rw [← map_commutatorElement, ← AutL2Facts.map_autEquiv_innAut e] at h1
  obtain ⟨x, hx, hxe⟩ := h1
  have := (AutL2Facts.autEquiv e).injective hxe
  rw [← this]
  exact hx

theorem isSolvable_kernel (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (hc : S ⊓ coreActionKernel L = zpowers t) :
    Group.IsSolvable ↥(centralizer ({t} : Set X) ⊓ coreActionKernel L) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K₀ := centralizer ({t} : Set X) ⊓ coreActionKernel L
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 ↥K₀))
  have hP2 : Nat.card (P : Subgroup ↥K₀) = 2 := by
    have := card_of_isSylowOf_kernel h hS hc (P := (P : Subgroup ↥K₀).map K₀.subtype) ⟨P, rfl⟩
    rwa [card_map_of_injective K₀.subtype_injective] at this
  obtain ⟨N, hNn, hNodd, -, hNcard⟩ := exists_odd_normal_complement P hP2
  have hNsol : Group.IsSolvable N :=
    CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hNodd))
  have hQ : Nat.card (↥K₀ ⧸ N) = 2 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup N
    rw [← hNcard] at h1
    have hpos : 0 < Nat.card N := Nat.card_pos
    have : Nat.card (↥K₀ ⧸ N) * Nat.card N = 2 * Nat.card N := by rw [← h1]; ring
    exact Nat.eq_of_mul_eq_mul_right hpos this
  have hcyc : IsCyclic (↥K₀ ⧸ N) := isCyclic_of_prime_card hQ
  have hQsol : Group.IsSolvable (↥K₀ ⧸ N) := Group.isSolvable_of_comm hcyc.commGroup.mul_comm
  exact Group.isSolvable_of_ker_le_range N.subtype (QuotientGroup.mk' N)
    (by rw [QuotientGroup.ker_mk', range_subtype])

theorem normal_subgroupOf (h : Config t L p f) :
    (L.subgroupOf (centralizer ({t} : Set X))).Normal :=
  (normal_subgroupOf_iff_le_normalizer h.le_centralizer).mpr (le_normalizer h)

theorem isSolvable_quotient (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (hc : S ⊓ coreActionKernel L = zpowers t) :
    have := normal_subgroupOf h
    Group.IsSolvable (↥(centralizer ({t} : Set X)) ⧸ L.subgroupOf (centralizer ({t} : Set X))) := by
  have := normal_subgroupOf h
  have := innAut_normal_aux (Bar L)
  set H := centralizer ({t} : Set X) with hH
  let g₀ : ↥H →* MulAut (Bar L) ⧸ innAut (Bar L) := (QuotientGroup.mk' _).comp (rho h)
  have hg₀ : L.subgroupOf H ≤ g₀.ker := by
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    have : x = ⟨((⟨x, hx⟩ : L) : X), h.le_centralizer hx⟩ := rfl
    rw [this, rho_of_mem h]
    exact ⟨_, rfl⟩
  let g := QuotientGroup.lift (L.subgroupOf H) g₀ hg₀
  let f : ↥(H ⊓ coreActionKernel L) →* ↥H ⧸ L.subgroupOf H :=
    (QuotientGroup.mk' _).comp (Subgroup.inclusion inf_le_left)
  have hOut : Group.IsSolvable (MulAut (Bar L) ⧸ innAut (Bar L)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have := commutator_mem_innAut h b⁻¹ a⁻¹
    rw [commutatorElement_def] at this
    convert this using 1
    group
  have hKsol := isSolvable_kernel h hS hc
  refine Group.isSolvable_of_ker_le_range f g ?_
  intro y hy
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
  have hy' : rho h x ∈ innAut (Bar L) := by
    have : g₀ x = 1 := hy
    rwa [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
  obtain ⟨z, hz⟩ := hy'
  obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective z
  have hlH : (l : X) ∈ H := h.le_centralizer l.2
  have hker : x * (⟨l, hlH⟩ : ↥H)⁻¹ ∈ (rho h).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, ← hz, ← rho_of_mem h l, mul_inv_cancel]
  rw [mem_ker_rho] at hker
  refine ⟨⟨_, (x * (⟨l, hlH⟩ : ↥H)⁻¹).2, hker⟩, ?_⟩
  change QuotientGroup.mk (x * (⟨l, hlH⟩ : ↥H)⁻¹) = QuotientGroup.mk x
  rw [QuotientGroup.eq]
  have : (x * (⟨l, hlH⟩ : ↥H)⁻¹)⁻¹ * x = ⟨l, hlH⟩ := by group
  rw [this]
  exact l.2

theorem residual_eq_of_core (h : Config t L p f) {S : Subgroup X}
    (hS : IsSylowOf 2 S (centralizer ({t} : Set X))) (hc : S ⊓ coreActionKernel L = zpowers t) :
    (perfectResidual ↥(centralizer ({t} : Set X))).map (centralizer ({t} : Set X)).subtype = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := normal_subgroupOf h
  have hsol := isSolvable_quotient h hS hc
  have hle : perfectResidual ↥(centralizer ({t} : Set X)) ≤
      L.subgroupOf (centralizer ({t} : Set X)) :=
    ((perfect_residual_characterization (G := ↥(centralizer ({t} : Set X)))).2.2.2.2.1 _).mp hsol
  have hperf : Group.IsPerfect ↥(L.subgroupOf (centralizer ({t} : Set X))) :=
    CatalogueBHeldSmallCore.pComponent_perfect 2 _ h.isPComponent
  have hge : L.subgroupOf (centralizer ({t} : Set X)) ≤
      perfectResidual ↥(centralizer ({t} : Set X)) :=
    (perfect_residual_transport (MonoidHom.id ↥(centralizer ({t} : Set X)))).2.2 _ hperf
  rw [le_antisymm hle hge, subgroupOf_map_subtype, inf_of_le_left h.le_centralizer]

end Residual

theorem dihedralStructure_of_core [Finite X] (h : Config t L p f)
    (hcore : ∀ S : Subgroup X, IsSylowOf 2 S (centralizer ({t} : Set X)) → CoreAt t L S) :
    DihedralStructure t L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := exists_isSylowOf 2 (centralizer ({t} : Set X))
  obtain ⟨hc, -, heven⟩ := hcore S hS
  refine ⟨card_sylow_coreActionKernel h hS hc, residual_eq_of_core h hS hc,
    normalizer_eq_of_core h hS hc, kernel_eq_of_core h hS hc, heven, fun T => ?_⟩
  obtain ⟨-, hfield, -⟩ := hcore _ ⟨T, rfl⟩
  exact hfield

end CFSG.ComponentClassification.HSDihedral
