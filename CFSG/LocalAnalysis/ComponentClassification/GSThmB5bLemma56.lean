module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bLemma55
public import CFSG.LocalAnalysis.ComponentClassification.GSThmB5bOrbit

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer
open scoped Pointwise commutatorElement

theorem even_card_of_isQuasisimple' {K : Type*} [Group K] [Finite K] (hK : IsQuasisimple K) :
    Even (Nat.card K) := by
  obtain ⟨-, hs, hnab⟩ := hK
  have heven := (SimpleEvenOrder.nonabelian_simple_even hnab).1
  obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (center K)
  rw [hk]
  exact heven.mul_right k

theorem eq_of_mem_zpowers_of_orderOf_eq_two {G : Type*} [Group G] {a y : G}
    (ha : orderOf a = 2) (hy : y ∈ zpowers a) (hy1 : y ≠ 1) : y = a := by
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
  have ha2 : a ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, ← ha, pow_orderOf_eq_one]
  rcases Int.even_or_odd k with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exfalso
    apply hy1
    rw [show m + m = 2 * m by ring, zpow_mul, ha2, one_zpow]
  · rw [zpow_add_one, zpow_mul, ha2, one_zpow, one_mul]

theorem iSup_subgroupOf_eq {G : Type*} [Group G] {ι : Sort*} {X : Subgroup G} {Y : ι → Subgroup G}
    (hY : ∀ i, Y i ≤ X) : (⨆ i, Y i).subgroupOf X = ⨆ i, (Y i).subgroupOf X := by
  apply map_injective X.subtype_injective
  rw [subgroupOf_map_subtype, Subgroup.map_iSup, inf_of_le_left (iSup_le hY)]
  congr 1
  funext i
  rw [subgroupOf_map_subtype, inf_of_le_left (hY i)]

namespace Hyp52

variable {H : Type} [Group H] [Finite H] (h : Hyp52 H)

theorem centralizer_P_eq (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion)
    (hCFc : CFProp23Center) : h.P ⊓ centralizer (h.S : Set H) = zpowers h.a := by
  apply le_antisymm
  · intro c hc
    obtain ⟨hcP, hcS⟩ := mem_inf.mp hc
    have hcB : c ∈ normalizer (h.B : Set H) :=
      centralizer_le_normalizer _ (Subgroup.centralizer_le h.B_le_S hcS)
    have hcT : c ∈ h.T ⊓ centralizer (h.Q : Set H) :=
      mem_inf.mpr ⟨mem_inf.mpr ⟨mem_inf.mpr ⟨h.P_le_S hcP, hcB⟩, hcP⟩,
        Subgroup.centralizer_le inf_le_left hcS⟩
    have hca := hCFc H h (h.table hB1 hCF23) hcT
    have hzm : c ∈ (zpowers h.a : Set H) * (h.B : Set H) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
        (zpowers_le.mpr h.a_mem_normalizer)]
      exact hca
    obtain ⟨y, hy, b, hb, rfl⟩ := Set.mem_mul.mp hzm
    have hyx : y * h.x = h.x * y := by
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hy
      exact ((Commute.zpow_left (show Commute h.a h.x from h.x_comm_a.symm) k)).eq
    have hcx : h.x * (y * b) = (y * b) * h.x := mem_centralizer_iff.mp hcS h.x h.x_mem
    have hbx : h.x * b * h.x⁻¹ = b := by
      have : y * (h.x * b) = y * (b * h.x) := by
        calc y * (h.x * b) = (y * h.x) * b := by group
          _ = (h.x * y) * b := by rw [hyx]
          _ = (y * b) * h.x := by rw [mul_assoc, hcx]
          _ = y * (b * h.x) := by group
      rw [mul_left_cancel this, mul_inv_cancel_right]
    have hb1 : b = 1 := by
      have hbB' : b ∈ conjugate h.B h.x := by
        rw [mem_conjugate_iff, hbx]
        exact hb
      exact mem_bot.mp (h.inf_conjugate_x ▸ mem_inf.mpr ⟨hb, hbB'⟩)
    rw [hb1, mul_one]
    exact hy
  · rw [zpowers_le]
    exact mem_inf.mpr ⟨h.a_mem_P, mem_centralizer_iff.mpr fun s hs => h.comm_a hs⟩

theorem le_coreActionKernel_of_ne {L : Subgroup H} (hL : L ≤ centralizer ({h.a} : Set H))
    (hLp : IsPComponent 2 (L.subgroupOf (centralizer ({h.a} : Set H)))) (hLJ : L ≠ h.J) :
    L ≤ coreActionKernel h.J := by
  set C := centralizer ({h.a} : Set H) with hC
  have hne : h.J.subgroupOf C ≠ L.subgroupOf C := by
    intro he
    rw [subgroupOf_inj, inf_of_le_left h.J_le, inf_of_le_left hL] at he
    exact hLJ he.symm
  obtain ⟨-, hdist⟩ := CatalogueBPrimeJoin.distinct_p_components_core_commutation 2
    Nat.prime_two _ _ h.isPComponent_J hLp
  obtain ⟨hLN, -, hcomm, -⟩ := hdist hne
  have hcore := CFSG.pPrimeCore_map_subgroupOf 2 h.J C h.J_le
  intro l hl
  have hlC : l ∈ C := hL hl
  refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
  · rw [mem_normalizer_iff]
    intro y
    have h1 := hLN (show (⟨l, hlC⟩ : C) ∈ L.subgroupOf C from hl)
    constructor
    · intro hy
      have hyC : y ∈ C := h.J_le hy
      have h2 := (mem_normalizer_iff.mp h1 ⟨y, hyC⟩).mp hy
      exact h2
    · intro hy
      have hyC : l * y * l⁻¹ ∈ C := h.J_le hy
      have hyC' : y ∈ C := by
        have := mul_mem (mul_mem (inv_mem hlC) hyC) hlC
        simpa [mul_assoc] using this
      have h2 := (mem_normalizer_iff.mp h1 ⟨y, hyC'⟩).mpr hy
      exact h2
  · have hjC : j ∈ C := h.J_le hj
    have h1 : ⁅(⟨j, hjC⟩ : C)⁻¹, (⟨l, hlC⟩ : C)⁻¹⁆ ∈ ⁅h.J.subgroupOf C, L.subgroupOf C⁆ :=
      Subgroup.commutator_mem_commutator (inv_mem (show (⟨j, hjC⟩ : C) ∈ h.J.subgroupOf C
        from hj)) (inv_mem (show (⟨l, hlC⟩ : C) ∈ L.subgroupOf C from hl))
    have h2 := (hcomm h1).1
    rw [← hcore]
    refine ⟨_, h2, ?_⟩
    simp only [subtype_apply, commutatorElement_def, coe_mul, coe_inv, inv_inv]

abbrev N0 : Subgroup H := centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H)

theorem conjugate_facts {L : Subgroup H} (hL : L ≤ centralizer ({h.a} : Set H))
    (hLp : IsPComponent 2 (L.subgroupOf (centralizer ({h.a} : Set H)))) (hLJ : L ≠ h.J)
    {n : H} (hn : n ∈ h.N0) :
    conjugate L n ≤ centralizer ({h.a} : Set H) ∧
      IsPComponent 2 ((conjugate L n).subgroupOf (centralizer ({h.a} : Set H))) ∧
      conjugate L n ≠ h.J := by
  obtain ⟨h1, h2⟩ := isPComponent_conjugate_centralizer_singleton hL hLp (mem_inf.mp hn).1
  refine ⟨h1, h2, fun he => hLJ ?_⟩
  have := congrArg (fun Y => conjugate Y n⁻¹) he
  simp only [conjugate_conjugate_inv] at this
  rw [this, conjugate_eq_of_mem_normalizer (inv_mem (mem_inf.mp hn).2)]

theorem conj_mem_orbit {L : Subgroup H} {m y : H} (hm : m ∈ h.N0)
    (hy : y ∈ ⨆ n ∈ h.N0, conjugate L n) : m⁻¹ * y * m ∈ ⨆ n ∈ h.N0, conjugate L n := by
  have hle : (⨆ n ∈ h.N0, conjugate L n).map (MulAut.conj m⁻¹).toMonoidHom ≤
      ⨆ n ∈ h.N0, conjugate L n := by
    rw [Subgroup.map_iSup]
    refine iSup_le fun n => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hn => ?_
    have : (conjugate L n).map (MulAut.conj m⁻¹).toMonoidHom = conjugate L (n * m) := by
      rw [← conjugate_conjugate]
      rfl
    rw [this]
    exact le_iSup₂_of_le (n * m) (mul_mem hn hm) le_rfl
  have := hle (mem_map_of_mem _ hy)
  simpa [MulAut.conj_apply] using this

theorem a_mem_orbit (hP : h.P ⊓ centralizer (h.S : Set H) = zpowers h.a) {L : Subgroup H}
    (hL : L ≤ centralizer ({h.a} : Set H))
    (hLp : IsPComponent 2 (L.subgroupOf (centralizer ({h.a} : Set H)))) (hLJ : L ≠ h.J) :
    h.a ∈ ⨆ n ∈ h.N0, conjugate L n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := ⨆ n ∈ h.N0, conjugate L n with hM
  have hMC : M ≤ coreActionKernel h.J := by
    refine iSup₂_le fun n hn => ?_
    obtain ⟨h1, h2, h3⟩ := h.conjugate_facts hL hLp hLJ hn
    exact h.le_coreActionKernel_of_ne h1 h2 h3
  have hLM : L ≤ M := by
    have : conjugate L 1 = L := conjugate_one L
    rw [← this]
    exact le_iSup₂_of_le (1 : H) (one_mem _) le_rfl
  have hLq : IsQuasisimple (OddBar L) :=
    ((CatalogueBPrimeJoin.pComponent_subgroupOf_iff 2 L _ hL).1 hLp).2.2
  have hLeven : Even (Nat.card L) := by
    have h1 := even_card_of_isQuasisimple' hLq
    obtain ⟨k, hk⟩ := Subgroup.card_quotient_dvd_card (pPrimeCore 2 ↥L)
    rw [hk]
    exact h1.mul_right k
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := L) 2 (even_iff_two_dvd.mp hLeven)
  have ht2 : orderOf (t : H) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have htN0 : (t : H) ∈ h.N0 :=
    mem_inf.mpr ⟨hL t.2, (mem_coreActionKernel.mp (hMC (hLM t.2))).1⟩
  have h2t : IsPGroup 2 (zpowers (t : H)) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht2, pow_one])
  obtain ⟨m, hm, hmS⟩ := exists_conjugate_le_of_sylow h.S_sylow (zpowers_le.mpr htN0) h2t
  set t' := m⁻¹ * (t : H) * m with ht'
  have ht'S : t' ∈ h.S := hmS (by
    rw [mem_conjugate_iff, show m * (m⁻¹ * (t : H) * m) * m⁻¹ = t by group]
    exact mem_zpowers _)
  have ht'M : t' ∈ M := h.conj_mem_orbit hm (hLM t.2)
  have ht'1 : t' ≠ 1 := by
    intro h1
    have : (t : H) = 1 := by
      calc (t : H) = m * t' * m⁻¹ := by rw [ht']; group
        _ = 1 := by rw [h1]; group
    rw [this, orderOf_one] at ht2
    exact absurd ht2 (by norm_num)
  set N : Subgroup h.S := M.subgroupOf h.S with hN
  have hNn : N.Normal := by
    constructor
    intro n hn s
    rw [hN, mem_subgroupOf] at hn ⊢
    have := h.conj_mem_orbit (m := (s : H)⁻¹) (inv_mem (h.S_le s.2)) hn
    rw [inv_inv] at this
    exact this
  have hN1 : N ≠ ⊥ := by
    intro hb
    have : (⟨t', ht'S⟩ : h.S) ∈ N := ht'M
    rw [hb] at this
    exact ht'1 (congrArg Subtype.val (mem_bot.mp this))
  have hnil : Group.IsNilpotent h.S := h.isPGroup_S.isNilpotent
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hN1)
  obtain ⟨huN, huZ⟩ := mem_inf.mp u.2
  have huM : ((u : h.S) : H) ∈ M := huN
  have huP : ((u : h.S) : H) ∈ h.P ⊓ centralizer (h.S : Set H) := by
    refine mem_inf.mpr ⟨mem_inf.mpr ⟨(u : h.S).2, hMC huM⟩, mem_centralizer_iff.mpr ?_⟩
    intro s hs
    have := Subgroup.mem_center_iff.mp huZ ⟨s, hs⟩
    exact congrArg Subtype.val this
  rw [hP] at huP
  have hu1' : ((u : h.S) : H) ≠ 1 := fun he => hu1 (Subtype.ext (Subtype.ext he))
  have := eq_of_mem_zpowers_of_orderOf_eq_two h.orderOf_a huP hu1'
  rw [← this]
  exact huM

theorem a_not_mem_orbit_of_center_eq_bot {L : Subgroup H}
    (hL : L ≤ centralizer ({h.a} : Set H))
    (hLp : IsPComponent 2 (L.subgroupOf (centralizer ({h.a} : Set H))))
    (hZ : center (OddBar L) = ⊥) : h.a ∉ ⨆ n ∈ h.N0, conjugate L n := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro ha
  set X := centralizer ({h.a} : Set H) with hX
  set π := QuotientGroup.mk' (pPrimeCore 2 ↥X) with hπ
  have hconj : ∀ n ∈ h.N0, conjugate L n ≤ X ∧
      IsPComponent 2 ((conjugate L n).subgroupOf X) := fun n hn =>
    isPComponent_conjugate_centralizer_singleton hL hLp (mem_inf.mp hn).1
  let Kc : H → Subgroup (↥X ⧸ pPrimeCore 2 ↥X) := fun n => ((conjugate L n).subgroupOf X).map π
  have hKcomp : ∀ n ∈ h.N0, IsComponent (Kc n) := by
    intro n hn
    obtain ⟨K', hK', -, hmap, -⟩ := (hconj n hn).2
    rw [show Kc n = K' from hmap]
    exact hK'
  have hKZ : ∀ n ∈ h.N0, center ↥(Kc n) = ⊥ := by
    intro n hn
    rw [eq_bot_iff]
    intro zb hzb
    obtain ⟨z, hz, hze⟩ := mem_map.mp zb.2
    have hzL : ((z : X) : H) ∈ conjugate L n := mem_subgroupOf.mp hz
    have hcomm : ∀ y ∈ conjugate L n, y⁻¹ * ((z : X) : H)⁻¹ * y * (z : X) ∈
        (pPrimeCore 2 X).map X.subtype := by
      intro y hy
      have hyX : y ∈ X := (hconj n hn).1 hy
      have h1 := Subgroup.mem_center_iff.mp hzb ⟨π ⟨y, hyX⟩, mem_map_of_mem π
        (show (⟨y, hyX⟩ : X) ∈ (conjugate L n).subgroupOf X from hy)⟩
      have h2 : π ⟨y, hyX⟩ * π z = π z * π ⟨y, hyX⟩ := by
        have := congrArg Subtype.val h1
        simp only [coe_mul] at this
        rw [hze]
        exact this
      rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq] at h2
      refine ⟨_, inv_mem h2, ?_⟩
      simp only [subtype_apply, coe_mul, coe_inv, mul_inv_rev, inv_inv]
      group
    have hzK : ((z : X) : H) ∈ conjugate L n ⊓ coreActionKernel (conjugate L n) := by
      refine mem_inf.mpr ⟨hzL, mem_coreActionKernel.mpr ⟨le_normalizer hzL, fun y hy => ?_⟩⟩
      have h3 : y⁻¹ * ((z : X) : H)⁻¹ * y * (z : X) ∈ conjugate L n :=
        mul_mem (mul_mem (mul_mem (inv_mem hy) (inv_mem hzL)) hy) hzL
      exact inf_oddCore_le (hconj n hn).1 (mem_inf.mpr ⟨h3, hcomm y hy⟩)
    have hzO := oddCore_le_of_isPComponent (hconj n hn).1 (hconj n hn).2
      (inf_coreActionKernel_le_of_center_eq_bot (center_oddBar_conjugate hZ n) hzK)
    obtain ⟨o, ho, hoe⟩ := mem_map.mp hzO
    have hzo : z = o := Subtype.ext hoe.symm
    apply mem_bot.mpr
    apply Subtype.ext
    rw [← hze, hzo]
    simp only [OneMemClass.coe_one]
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact ho
  let F : Finset (Subgroup (↥X ⧸ pPrimeCore 2 ↥X)) :=
    (Set.toFinite (Kc '' (h.N0 : Set H))).toFinset
  have hF : ∀ A ∈ F, ∃ n ∈ h.N0, A = Kc n := by
    intro A hA
    obtain ⟨n, hn, rfl⟩ := (Set.Finite.mem_toFinset _).mp hA
    exact ⟨n, hn, rfl⟩
  have hFZ : ∀ A ∈ F, center ↥A = ⊥ := by
    intro A hA
    obtain ⟨n, hn, rfl⟩ := hF A hA
    exact hKZ n hn
  have hFc : ∀ A ∈ F, ∀ B ∈ F, A ≠ B → ⁅A, B⁆ = ⊥ := by
    intro A hA B hB hAB
    obtain ⟨n, hn, rfl⟩ := hF A hA
    obtain ⟨m, hm, rfl⟩ := hF B hB
    rcases CFSG.LocalCores.distinct_components_commute (hKcomp n hn) (hKcomp m hm) with h1 | h1
    · exact absurd h1 hAB
    · exact h1
  have haX : h.a ∈ X := mem_centralizer_singleton_iff.mpr rfl
  have hmem : π ⟨h.a, haX⟩ ∈ ⨆ A ∈ F, A := by
    have h1 : (⟨h.a, haX⟩ : X) ∈ (⨆ n ∈ h.N0, conjugate L n).subgroupOf X := ha
    have hle : ∀ n, (⨆ (_ : n ∈ h.N0), conjugate L n) ≤ X := fun n =>
      iSup_le fun hn => (hconj n hn).1
    rw [iSup_subgroupOf_eq hle] at h1
    have h2 := mem_map_of_mem π h1
    rw [Subgroup.map_iSup] at h2
    refine (iSup_le fun n => ?_ : _ ≤ ⨆ A ∈ F, A) h2
    rw [iSup_subgroupOf_eq (fun hn : n ∈ h.N0 => (hconj n hn).1), Subgroup.map_iSup]
    refine iSup_le fun hn => ?_
    exact le_iSup₂_of_le (Kc n) ((Set.Finite.mem_toFinset _).mpr ⟨n, hn, rfl⟩) le_rfl
  have hcen : ∀ y ∈ ⨆ A ∈ F, A, π ⟨h.a, haX⟩ * y = y * π ⟨h.a, haX⟩ := by
    intro y _
    induction y using QuotientGroup.induction_on with
    | H y =>
      have hy := mem_centralizer_singleton_iff.mp y.2
      show π ⟨h.a, haX⟩ * π y = π y * π ⟨h.a, haX⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hy.symm
  have h1 := eq_one_of_mem_iSup_of_commute F hFZ hFc hmem hcen
  rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have hodd := CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥X)
  have hdvd : orderOf (⟨⟨h.a, haX⟩, h1⟩ : pPrimeCore 2 ↥X) ∣ Nat.card (pPrimeCore 2 ↥X) :=
    orderOf_dvd_natCard _
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, h.orderOf_a] at hdvd
  exact absurd (Nat.Coprime.coprime_dvd_right hdvd hodd) (by norm_num)

theorem center_ne_bot_of_ne (hB1 : ConjFixStatement) (hCF23 : CFProp23Fusion)
    (hCFc : CFProp23Center) {L : Subgroup H} (hL : L ≤ centralizer ({h.a} : Set H))
    (hLp : IsPComponent 2 (L.subgroupOf (centralizer ({h.a} : Set H)))) (hLJ : L ≠ h.J) :
    center (OddBar L) ≠ ⊥ := fun hZ =>
  h.a_not_mem_orbit_of_center_eq_bot hL hLp hZ
    (h.a_mem_orbit (h.centralizer_P_eq hB1 hCF23 hCFc) hL hLp hLJ)

theorem centralizer_le_normalizer_J (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) :
    centralizer ({h.a} : Set H) ≤ normalizer (h.J : Set H) := by
  intro g hg
  by_contra hgN
  have hne : conjugate h.J g⁻¹ ≠ h.J := by
    intro he
    apply hgN
    have := congrArg (fun Y => conjugate Y g) he
    simp only [show ∀ Y : Subgroup H, conjugate (conjugate Y g⁻¹) g = Y from fun Y => by
      rw [conjugate_conjugate, inv_mul_cancel, conjugate_one]] at this
    exact mem_normalizer_of_conjugate_eq this.symm
  obtain ⟨h1, h2⟩ := isPComponent_conjugate_centralizer_singleton h.J_le h.isPComponent_J
    (inv_mem hg)
  exact h.center_ne_bot_of_ne hB1 hCF23 hCFc h1 h2 hne
    (center_oddBar_conjugate (h.center_eq_bot hB1 hB6 hCF23 hCF24) g⁻¹)

theorem S_sylow_centralizer (hB1 : ConjFixStatement) (hB6 : SylowKernelStatement)
    (hCF23 : CFProp23Fusion) (hCF24 : CFProp24c) (hCFc : CFProp23Center) :
    h.S ≤ centralizer ({h.a} : Set H) ∧ ∃ R : Sylow 2 ↥(centralizer ({h.a} : Set H)),
      (R : Subgroup _) = h.S.subgroupOf (centralizer ({h.a} : Set H)) := by
  have heq : centralizer ({h.a} : Set H) ⊓ normalizer (h.J : Set H) =
      centralizer ({h.a} : Set H) :=
    inf_of_le_left (h.centralizer_le_normalizer_J hB1 hB6 hCF23 hCF24 hCFc)
  have hS := h.S_sylow
  rw [heq] at hS
  exact ⟨h.S_le.trans inf_le_left, hS⟩

end Hyp52

end CFSG.ComponentClassification.GSThmB
