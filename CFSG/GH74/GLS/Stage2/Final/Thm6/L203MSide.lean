module

public import CFSG.GH74.GLS.Stage2.Final.Thm4.Core
public import CFSG.GH74.GLS.Stage2.Final.Thm6.Defs
public import CFSG.GH74.GLS.Stage2.Local.Bar

public section

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.GLS.Stage2.Local CFSG.LocalCores
open CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Bg CFSG.GH74.GLS.Stage12 CFSG.Blueprint CFSG.Assembly.LowTwoRank

namespace CFSG.GH74.GLS.Stage2.Final.Thm6.L203

section LayerFacts

theorem center_eq_bot_of_simple {X : Type} [Group X] [IsSimpleGroup X] (h : ∃ a b : X, a * b ≠ b * a) :
    Subgroup.center X = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with hb | ht
  · exact hb
  · exfalso
    obtain ⟨a, b, hab⟩ := h
    apply hab
    have : a ∈ Subgroup.center X := by rw [ht]; exact Subgroup.mem_top a
    exact (Subgroup.mem_center_iff.1 this b).symm

variable {Y : Type} [Group Y] [Finite Y]

theorem layerFacts
    (hS : IsSimpleGroup ↥(generalizedFitting (Y ⧸ pPrimeCore 2 Y)))
    (hSn : ∃ a b : ↥(generalizedFitting (Y ⧸ pPrimeCore 2 Y)), a * b ≠ b * a)
    (hK : layer Y ≠ ⊥) (hE : IsSimpleGroup ↥(layer Y)) (hEn : ∃ a b : ↥(layer Y), a * b ≠ b * a) :
    (∀ e ∈ layer Y, e ∈ pPrimeCore 2 Y → e = 1) ∧
    (∀ c : Y, (∀ e ∈ layer Y, c * e = e * c) → c ∈ pPrimeCore 2 Y) ∧
    (∀ y : Y, (QuotientGroup.mk y : Y ⧸ pPrimeCore 2 Y) ∈ generalizedFitting (Y ⧸ pPrimeCore 2 Y) →
      ∃ e ∈ layer Y, ∃ a ∈ pPrimeCore 2 Y, y = e * a) := by
  set π : Y →* Y ⧸ pPrimeCore 2 Y := QuotientGroup.mk' (pPrimeCore 2 Y) with hπ
  have hmap := map_layer_eq hS hK
  refine ⟨?_, ?_, ?_⟩
  · intro e he hA
    have hnormal : ((layer Y ⊓ pPrimeCore 2 Y).subgroupOf (layer Y)).Normal := by
      rw [Subgroup.inf_subgroupOf_left]
      exact Subgroup.Normal.subgroupOf inferInstance _
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((layer Y ⊓ pPrimeCore 2 Y).subgroupOf (layer Y)) with hb | ht
    · have h1 : (⟨e, he⟩ : ↥(layer Y)) ∈ (layer Y ⊓ pPrimeCore 2 Y).subgroupOf (layer Y) :=
        Subgroup.mem_subgroupOf.2 ⟨he, hA⟩
      rw [hb, Subgroup.mem_bot] at h1
      exact congrArg Subtype.val h1
    · exfalso
      have hle : layer Y ≤ pPrimeCore 2 Y := by
        intro x hx
        have : (⟨x, hx⟩ : ↥(layer Y)) ∈ (layer Y ⊓ pPrimeCore 2 Y).subgroupOf (layer Y) := by
          rw [ht]; exact Subgroup.mem_top _
        exact (Subgroup.mem_subgroupOf.1 this).2
      have hodd : Odd (Nat.card ↥(pPrimeCore 2 Y)) :=
        Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := Y))
      have hodd' : Odd (Nat.card ↥(layer Y)) :=
        Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hle)
      have hsolv : Group.IsSolvable ↥(layer Y) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd'
      obtain ⟨a, b, hab⟩ := hEn
      exact hab (IsSimpleGroup.comm_iff_isSolvable.2 hsolv a b)
  · intro c hc
    have hc1 : π c ∈ Subgroup.centralizer (generalizedFitting (Y ⧸ pPrimeCore 2 Y) : Set (Y ⧸ pPrimeCore 2 Y)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [← hmap] at hg
      obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 hg
      show π e * π c = π c * π e
      rw [← map_mul, ← map_mul, hc e he]
    have hc2 := CFSG.centralizer_generalizedFitting_le _ hc1
    have hcen : (⟨π c, hc2⟩ : ↥(generalizedFitting (Y ⧸ pPrimeCore 2 Y))) ∈ Subgroup.center _ := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.1 hc1 g g.2)
    rw [center_eq_bot_of_simple hSn, Subgroup.mem_bot] at hcen
    exact (QuotientGroup.eq_one_iff c).1 (congrArg Subtype.val hcen)
  · intro y hy
    rw [← hmap] at hy
    obtain ⟨e, he, hey⟩ := Subgroup.mem_map.1 hy
    refine ⟨e, he, e⁻¹ * y, ?_, by group⟩
    have : π e = π y := hey
    rw [← QuotientGroup.eq]
    exact this

end LayerFacts

section NormalPGroup

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_normal_pgroup_of_odd (A : Subgroup Y) [A.Normal] (hA1 : A ≠ ⊥) (hAodd : Odd (Nat.card A)) :
    ∃ (r : ℕ) (Q : Subgroup Y), r.Prime ∧ r ≠ 2 ∧ Q ≤ A ∧ IsPGroup r ↥Q ∧ Q ≠ ⊥ ∧ Q.Normal := by
  have hsolv : Group.IsSolvable ↥A := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hAodd
  have hcard1 : Nat.card ↥A ≠ 1 := by
    intro h
    exact hA1 (Subgroup.eq_bot_of_card_eq A h)
  have hF : fittingSubgroup ↥A ≠ ⊥ := fun h =>
    hcard1 ((fitting_eq_bot_iff_card_eq_one_of_solvable ↥A).1 h)
  rw [fitting_eq_sup_pCore, Ne, iSup_eq_bot] at hF
  push Not at hF
  obtain ⟨p, hp⟩ := hF
  have hpr : p.1.1.Prime := Nat.prime_of_mem_primeFactors p.1.2
  have hpne : pCore p.1.1 ↥A ≠ ⊥ := hp
  refine ⟨p.1.1, (pCore p.1.1 ↥A).map A.subtype, hpr, ?_, Subgroup.map_subtype_le _, ?_, ?_, ?_⟩
  · intro h2
    have hQ : IsPGroup p.1.1 (pCore p.1.1 ↥A) := pCore_isPGroup
    have : Fact p.1.1.Prime := ⟨hpr⟩
    obtain ⟨k, hk⟩ := hQ.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      exact hpne (Subgroup.eq_bot_of_card_eq _ (by simpa using hk))
    have hdvd : p.1.1 ∣ Nat.card ↥(pCore p.1.1 ↥A) := by
      rw [hk]; exact dvd_pow_self _ hk0
    have h3 : p.1.1 ∣ Nat.card ↥A := hdvd.trans (Subgroup.card_subgroup_dvd_card _)
    rw [h2] at h3
    exact (Nat.not_even_iff_odd.2 hAodd) (even_iff_two_dvd.2 h3)
  · exact (pCore_isPGroup).map A.subtype
  · intro h
    apply hpne
    rw [eq_bot_iff]
    intro x hx
    have : A.subtype x ∈ (pCore p.1.1 ↥A).map A.subtype := Subgroup.mem_map_of_mem _ hx
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  · refine ⟨fun x hx y => ?_⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hx
    have h1 := Subgroup.characteristic_iff_map_eq.mp
      (pCore_characteristic (G := ↥A) (p := p.1.1)) (MulAut.conjNormal (H := A) y)
    have h2 : (MulAut.conjNormal (H := A) y) a ∈ pCore p.1.1 ↥A := by
      rw [← h1]; exact Subgroup.mem_map_of_mem _ ha
    exact Subgroup.mem_map.2 ⟨_, h2, by simp [MulAut.conjNormal_apply]⟩

end NormalPGroup


section Abstract

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_noncomm_of_simple_perfect {K : Type} [Group K] [IsSimpleGroup K]
    (hp : Group.IsPerfect K) : ∃ a b : K, a * b ≠ b * a := by
  by_contra h
  have hc : ∀ a b : K, a * b = b * a := fun a b => by
    by_contra hab
    exact h ⟨a, b, hab⟩
  have hsolv : Group.IsSolvable K := IsSimpleGroup.comm_iff_isSolvable.1 hc
  have := hp
  have := IsSimpleGroup.toNontrivial (G := K)
  exact Group.IsPerfect.not_isSolvable K hsolv

theorem layer_odd_facts
    (hS : IsSimpleGroup ↥(generalizedFitting (Y ⧸ pPrimeCore 2 Y)))
    (hSn : ∃ a b : ↥(generalizedFitting (Y ⧸ pPrimeCore 2 Y)), a * b ≠ b * a)
    (hK : layer Y ≠ ⊥) (hE : IsSimpleGroup ↥(layer Y)) (hEn : ∃ a b : ↥(layer Y), a * b ≠ b * a) :
    (∀ e ∈ layer Y, ∀ a ∈ pPrimeCore 2 Y, e * a = a * e) ∧
    (∀ c : Y, (∀ e ∈ layer Y, c * e = e * c) → c ∈ pPrimeCore 2 Y) ∧
    (∀ y : Y, orderOf y = 2 → (QuotientGroup.mk y : Y ⧸ pPrimeCore 2 Y) ∈
      generalizedFitting (Y ⧸ pPrimeCore 2 Y) → y ∈ layer Y) := by
  obtain ⟨h1, h2, h3⟩ := layerFacts hS hSn hK hE hEn
  have hAodd : Odd (Nat.card ↥(pPrimeCore 2 Y)) :=
    Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := Y))
  have hcomm : ∀ e ∈ layer Y, ∀ a ∈ pPrimeCore 2 Y, e * a = a * e := by
    intro e he a ha
    have hLc : (layer Y).Characteristic := layer_characteristic
    have hLn : (layer Y).Normal := inferInstance
    have hAn : (pPrimeCore 2 Y).Normal := inferInstance
    have hcE : e * a * e⁻¹ * a⁻¹ ∈ layer Y := by
      have : e * (a * e⁻¹ * a⁻¹) ∈ layer Y :=
        (layer Y).mul_mem he (hLn.conj_mem _ ((layer Y).inv_mem he) a)
      simpa [mul_assoc] using this
    have hcA : e * a * e⁻¹ * a⁻¹ ∈ pPrimeCore 2 Y :=
      (pPrimeCore 2 Y).mul_mem (hAn.conj_mem _ ha e) ((pPrimeCore 2 Y).inv_mem ha)
    have hc1 : e * a * e⁻¹ * a⁻¹ = 1 := h1 _ hcE hcA
    calc e * a = (e * a * e⁻¹ * a⁻¹) * (a * e) := by group
      _ = a * e := by rw [hc1, one_mul]
  refine ⟨hcomm, h2, ?_⟩
  intro y hy2 hyF
  obtain ⟨e, he, a, ha, rfl⟩ := h3 y hyF
  have hsq : (e * a) * (e * a) = 1 := by
    have := pow_orderOf_eq_one (e * a)
    rwa [hy2, pow_two] at this
  have hsq' : (e * e) * (a * a) = 1 := by
    calc (e * e) * (a * a) = e * (e * a) * a := by group
      _ = e * (a * e) * a := by rw [hcomm e he a ha]
      _ = (e * a) * (e * a) := by group
      _ = 1 := hsq
  have hee : e * e = 1 := by
    have hA' : e * e = (a * a)⁻¹ := eq_inv_of_mul_eq_one_left hsq'
    apply h1 (e * e) ((layer Y).mul_mem he he)
    rw [hA']
    exact (pPrimeCore 2 Y).inv_mem ((pPrimeCore 2 Y).mul_mem ha ha)
  have haa : a * a = 1 := by
    rw [hee, one_mul] at hsq'
    exact hsq'
  have ha1 : a = 1 := by
    have h2d : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact haa)
    have h2o : orderOf a ∣ Nat.card ↥(pPrimeCore 2 Y) := Subgroup.orderOf_dvd_natCard _ ha
    have hodd : Odd (orderOf a) := Odd.of_dvd_nat hAodd h2o
    have : orderOf a = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 h2d with h | h
      · exact h
      · rw [h] at hodd
        exact absurd hodd (by decide)
    exact orderOf_eq_one_iff.1 this
  rw [ha1, mul_one]
  exact he

end Abstract

section Maximal

variable {G : Type} [Group G]

theorem mem_of_centralizes_normal [IsSimpleGroup G] {M Q : Subgroup G} (hM : IsCoatom M) (hQM : Q ≤ M)
    (hQ1 : Q ≠ ⊥) (hQn : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q) :
    ∀ x : G, (∀ q ∈ Q, x * q = q * x) → x ∈ M := by
  have hMN : M ≤ Subgroup.normalizer (Q : Set G) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro q
    refine ⟨fun hq => hQn m hm q hq, fun h => ?_⟩
    have := hQn m⁻¹ (M.inv_mem hm) _ h
    simpa [mul_assoc] using this
  have hNM : Subgroup.normalizer (Q : Set G) ≤ M := by
    by_contra hnot
    have hlt : M < Subgroup.normalizer (Q : Set G) :=
      lt_of_le_of_ne hMN (fun h' => hnot (h' ▸ le_rfl))
    have htop : Subgroup.normalizer (Q : Set G) = ⊤ := hM.2 _ hlt
    have hQnormal : Q.Normal := (Subgroup.normalizer_eq_top_iff).1 htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Q with hb | ht
    · exact hQ1 hb
    · rw [ht] at hQM
      exact hM.1 (top_le_iff.1 hQM)
  intro x hx
  apply hNM
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · intro hq
    have h2 : x * q * x⁻¹ = q := by rw [hx q hq]; group
    rw [h2]
    exact hq
  · intro hp
    have h1 : x * (x * q * x⁻¹) = (x * q * x⁻¹) * x := hx _ hp
    have h2 : x * q * x⁻¹ = q := by
      calc x * q * x⁻¹ = x⁻¹ * (x * (x * q * x⁻¹)) := by group
        _ = x⁻¹ * ((x * q * x⁻¹) * x) := by rw [h1]
        _ = q := by group
    rw [h2] at hp
    exact hp

end Maximal

section Involutions

variable {G : Type} [Group G]

theorem exists_involution_ne_of_fourSubgroup {V : Subgroup G} (hV : IVK.IsFourSubgroup V) (z : G) :
    ∃ v ∈ V, orderOf v = 2 ∧ v ≠ z := by
  obtain ⟨hel, hcard⟩ := hV
  have hsub : ¬ ∀ v ∈ V, v = 1 ∨ v = z := by
    intro h
    have hle : (V : Set G) ⊆ {1, z} := fun v hv => by
      rcases h v hv with rfl | rfl <;> simp
    have h1 : (V : Set G).ncard ≤ ({1, z} : Set G).ncard := Set.ncard_le_ncard hle (Set.toFinite _)
    have h2 : ({1, z} : Set G).ncard ≤ 2 := by
      have := Set.ncard_insert_le (1 : G) ({z} : Set G)
      rw [Set.ncard_singleton] at this
      exact this
    have h3 : Nat.card ↥V = (V : Set G).ncard := Nat.card_coe_set_eq _
    omega
  push Not at hsub
  obtain ⟨v, hv, hv1, hvz⟩ := hsub
  refine ⟨v, hv, ?_, hvz⟩
  have : IsElementaryAbelian 2 ↥V := hel
  have hv2 : v ^ 2 = 1 := elemPow_eq_one_of_isElementaryAbelian v hv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact orderOf_eq_prime hv2 hv1

theorem isCentralInvolution_of_isConj' {z x : G} (hz : IsCentralInvolution z) (h : IsConj z x) :
    IsCentralInvolution x := by
  obtain ⟨hord, S₀, hzS, hzc⟩ := hz
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine ⟨?_, c • S₀, ?_, ?_⟩
  · have h1 := MulEquiv.orderOf_eq (MulAut.conj c) z
    rw [MulAut.conj_apply] at h1
    rw [← hc, h1]
    exact hord
  · rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    exact ⟨z, hzS, by rw [← hc]; rfl⟩
  · intro s hs
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hs
    obtain ⟨s', hs', rfl⟩ := hs
    have := hzc s' hs'
    rw [← hc]
    show (c * s' * c⁻¹) * (c * z * c⁻¹) = (c * z * c⁻¹) * (c * s' * c⁻¹)
    calc (c * s' * c⁻¹) * (c * z * c⁻¹) = c * (s' * z) * c⁻¹ := by group
      _ = c * (z * s') * c⁻¹ := by rw [this]
      _ = (c * z * c⁻¹) * (c * s' * c⁻¹) := by group

end Involutions

section MSideSec

variable {G : Type} [Group G] [Finite G]

structure MSide (z : G) (M : Subgroup G) (q : ℕ) : Prop where
  psp4 : IVK.IsPSp4 ↥(Em M) q
  norm : ∀ m ∈ M, ∀ e ∈ Em M, m * e * m⁻¹ ∈ Em M
  cent : ∀ c ∈ M, (∀ e ∈ Em M, c * e = e * c) → c ∈ pPrimeCoreOf 2 M
  comm : ∀ e ∈ Em M, ∀ a ∈ pPrimeCoreOf 2 M, e * a = a * e
  invol : ∃ t : G, orderOf t = 2 ∧ ¬ IsConj z t ∧ t ∈ Em M ∧
    ∀ u : G, orderOf u = 2 → ¬ IsConj z u → IsConj t u
  normal : ∃ (r : ℕ) (Q : Subgroup G), r.Prime ∧ r ≠ 2 ∧ Q ≤ pPrimeCoreOf 2 M ∧ IsPGroup r ↥Q ∧ Q ≠ ⊥ ∧
    (∀ m ∈ M, ∀ x ∈ Q, m * x * m⁻¹ ∈ Q) ∧ (∀ x : G, (∀ y ∈ Q, x * y = y * x) → x ∈ M)

theorem mside {z : G} {k : Kind} {S M : Subgroup G} (h34 : Leaf_Prop34) (h : Fail20 G z k S M)
    (hne : M ≠ Cen z) :
    ∃ (ε : Bool) (q : ℕ) (L₁ L₂ : Subgroup (CentralizerBar z)), k = Kind.l4 ε ∧
      Stage1L4 G z S ε q L₁ L₂ ∧ q % 4 = (if ε then 3 else 1) ∧ 3 < q ∧ MSide z M q := by
  have hc17 : Ctx17 G z k S M := h.ctx.ctx17
  have hP34 := h34 G z k S hc17.ctx M hc17.cen_le hc17.ne_top
  rcases hP34 with hc | hd | ⟨ε, q, L₁, L₂, hk, hL4, hmod, hq3, hF, hcoat, hLF, -, -, -⟩
  · exact absurd (hc17.eq_of_oddCover hc) hne
  · exact absurd hd (not_isDihedral_S hc17.ctx)
  · refine ⟨ε, q, L₁, L₂, hk, hL4, hmod, hq3, ?_⟩
    have hlt : Cen z < M := lt_of_le_of_ne hc17.cen_le (Ne.symm hne)
    have hPS : IVK.IsPSp4 ↥(Em M) q := (h.ctx.thm4.2.1 hlt).2.2 ε q L₁ L₂ hk hL4
    obtain ⟨hES, hEP⟩ := isSimple_isPerfect_of_isPSp4 hq3 hPS
    obtain ⟨hFS, hFP⟩ := isSimple_isPerfect_of_isPSp4 hq3 hF
    let eE : ↥(layer ↥M) ≃* ↥(Em M) :=
      Subgroup.equivMapOfInjective (layer ↥M) M.subtype M.subtype_injective
    have hE : IsSimpleGroup ↥(layer ↥M) := eE.isSimpleGroup_congr.2 hES
    have hEn : ∃ a b : ↥(layer ↥M), a * b ≠ b * a :=
      exists_noncomm_of_simple_perfect (layer_isPerfect (G := ↥M))
    have hK : layer ↥M ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 hE.toNontrivial
    have hSn : ∃ a b : ↥(generalizedFitting (↥M ⧸ pPrimeCore 2 ↥M)), a * b ≠ b * a :=
      exists_noncomm_of_simple_perfect hFP
    obtain ⟨hcomm, hcent, hinv⟩ := layer_odd_facts (Y := ↥M) hFS hSn hK hE hEn
    have hLc : (layer ↥M).Characteristic := layer_characteristic
    refine ⟨hPS, ?_, ?_, ?_, ?_, ?_⟩
    · intro m hm e he
      obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.1 he
      have := (inferInstance : (layer ↥M).Normal).conj_mem e' he' ⟨m, hm⟩
      exact Subgroup.mem_map.2 ⟨_, this, rfl⟩
    · intro c hc hcE
      have h1 : (⟨c, hc⟩ : ↥M) ∈ pPrimeCore 2 ↥M := by
        apply hcent
        intro e' he'
        apply Subtype.ext
        exact hcE (e' : G) (Subgroup.mem_map.2 ⟨e', he', rfl⟩)
      exact Subgroup.mem_map.2 ⟨_, h1, rfl⟩
    · intro e he a ha
      obtain ⟨e', he', rfl⟩ := Subgroup.mem_map.1 he
      obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.1 (show a ∈ (pPrimeCore 2 ↥M).map M.subtype from ha)
      exact congrArg Subtype.val (hcomm e' he' a' ha')
    ·
      have hx₀ : ∃ x₀ : G, TwoClassData G z S L₁ L₂ q x₀ := by
        rcases hL4.fusion with ⟨h1, -⟩ | ⟨-, x₀, hx₀, -⟩
        · exfalso
          cases ε <;> simp at h1 hmod <;> omega
        · exact ⟨x₀, hx₀⟩
      obtain ⟨x₀, hx₀⟩ := hx₀
      obtain ⟨t₁, ht₁S, ht₁c, ht₁sw⟩ := hx₀.swap_exists
      obtain ⟨-, -, -, V, hVL, hV4, -, -⟩ := hx₀.swap_conseq t₁ ht₁S ht₁c ht₁sw
      obtain ⟨v, hvV, hv2, hvz⟩ := exists_involution_ne_of_fourSubgroup hV4 z
      have hvL : v ∈ LC z := hVL hvV
      obtain ⟨hxv, -⟩ := hx₀.invol_L v hvL hv2 hvz
      have hnc : ¬ IsConj z v := by
        intro hzv
        exact hx₀.x_nonCentral (isCentralInvolution_of_isConj' hc17.ctx.central (hzv.trans hxv.symm))
      have hvM : v ∈ M := hc17.cen_le (LC_le_Cen z hvL)
      have hvbar : (QuotientGroup.mk ⟨v, hvM⟩ : ↥M ⧸ pPrimeCore 2 ↥M) ∈
          generalizedFitting (↥M ⧸ pPrimeCore 2 ↥M) := by
        apply hLF
        exact Subgroup.mem_map.2 ⟨⟨v, hvM⟩, Subgroup.mem_subgroupOf.2 hvL, rfl⟩
      have hvE : (⟨v, hvM⟩ : ↥M) ∈ layer ↥M :=
        hinv _ (by rw [Subgroup.orderOf_mk]; exact hv2) hvbar
      exact ⟨v, hv2, hnc, Subgroup.mem_map.2 ⟨_, hvE, rfl⟩,
        fun u hu hnu => hxv.symm.trans ((hx₀.classes u hu).resolve_left hnu)⟩
    ·
      have hA1 : pPrimeCore 2 ↥M ≠ ⊥ := by
        intro hb
        apply h.odd_ne
        show (pPrimeCore 2 ↥M).map M.subtype = ⊥
        rw [hb, Subgroup.map_bot]
      have hAodd : Odd (Nat.card ↥(pPrimeCore 2 ↥M)) :=
        Nat.coprime_two_left.1 (pPrimeCore_coprime_card (p := 2) (G := ↥M))
      obtain ⟨r, Q', hr, hr2, hQ'A, hQ'p, hQ'1, hQ'n⟩ :=
        exists_normal_pgroup_of_odd (pPrimeCore 2 ↥M) hA1 hAodd
      have hQ1 : Q'.map M.subtype ≠ ⊥ := by
        intro hb
        exact hQ'1 (Subgroup.map_injective M.subtype_injective (hb.trans (Subgroup.map_bot _).symm))
      have hQn : ∀ m ∈ M, ∀ x ∈ Q'.map M.subtype, m * x * m⁻¹ ∈ Q'.map M.subtype := by
        intro m hm x hx
        obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hx
        exact Subgroup.mem_map.2 ⟨_, hQ'n.conj_mem x' hx' ⟨m, hm⟩, rfl⟩
      have : IsSimpleGroup G := hc17.ctx.std.kps.1
      exact ⟨r, Q'.map M.subtype, hr, hr2, Subgroup.map_mono hQ'A, hQ'p.map M.subtype, hQ1, hQn,
        mem_of_centralizes_normal hc17.mem.1 (Subgroup.map_subtype_le _) hQ1 hQn⟩

end MSideSec

end CFSG.GH74.GLS.Stage2.Final.Thm6.L203
