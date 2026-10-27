module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Tools
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Basic
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T23Defs

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T23

open CFSG Subgroup Assembly.LowTwoRank GH74.GLS.TwoThin

theorem isSLTwoOver_of_mulEquiv {q : ℕ} {A B : Type} [Group A] [Group B] (e : A ≃* B)
    (h : IsSLTwoOver q B) : IsSLTwoOver q A := by
  obtain ⟨F, _, _, hF, ⟨e'⟩⟩ := h
  exact ⟨F, inferInstance, inferInstance, hF, ⟨e.trans e'⟩⟩

variable {M : Type} [Group M] [Finite M]

theorem slTwo_of_diag (hGA : TBLit.GriessMultipliersAllModels) {t : M} (ht : orderOf t = 2)
    {K₀ : Subgroup M} (hK₀ : IsTwoComponent K₀) (hne : K₀.map (MulAut.conj t).toMonoidHom ≠ K₀)
    {p k : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hk : 1 ≤ k) (h5 : 5 ≤ p ^ k)
    (hsl : IsSLTwoOver (p ^ k)
      (↥(centralizerResidual (K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom) t) ⧸
        pPrimeCore 2 ↥(centralizerResidual (K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom) t))) :
    IsSLTwoOver (p ^ k) (↥K₀ ⧸ pPrimeCore 2 ↥K₀) := by
  obtain ⟨φ, hφ⟩ := L219.part_b3 ht ((L219.isTwoComponent_iff_twoComponents K₀).mp hK₀) hne
  obtain ⟨hBq, hBZ, hBm, -⟩ := Lemma47.sl2_facts hp hp2 hk h5 hsl
  have hQq : IsQuasisimple (↥K₀ ⧸ pPrimeCore 2 ↥K₀) := hK₀.2.2
  have hQo : Open.IsQuasisimple (↥K₀ ⧸ pPrimeCore 2 ↥K₀) :=
    (AssemblyBPredicates.isQuasisimple_iff_open _).mp
      ((AssemblyBPredicates.isQuasisimple_iff_native _).mpr hQq)
  have hker : φ.ker ≤ center (↥K₀ ⧸ pPrimeCore 2 ↥K₀) := by
    rcases Quasisimple.normal_le_center_or_eq_top hQo φ.ker with hc | htop
    · exact hc
    · exfalso
      have : Nontrivial (↥(centralizerResidual (K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom) t) ⧸
          pPrimeCore 2 ↥(centralizerResidual (K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom) t)) :=
        LocalCores.isQuasisimple_nontrivial hBq
      obtain ⟨a, b, hab⟩ := exists_pair_ne (↥(centralizerResidual
        (K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom) t) ⧸
          pPrimeCore 2 ↥(centralizerResidual (K₀ ⊔ K₀.map (MulAut.conj t).toMonoidHom) t))
      obtain ⟨x, rfl⟩ := hφ a
      obtain ⟨y, rfl⟩ := hφ b
      have hx : x ∈ φ.ker := htop ▸ mem_top x
      have hy : y ∈ φ.ker := htop ▸ mem_top y
      rw [MonoidHom.mem_ker] at hx hy
      exact hab (by rw [hx, hy])
  obtain ⟨e⟩ := LocalAnalysis.ComponentInitial.center_quotient_equiv_of_surjective hQq φ hφ hker
  obtain ⟨eZ⟩ := L35.nonempty_fusionZStar_quotient_equiv ↥K₀
  have hm : Blueprint.LieModel (↥K₀ ⧸ Open.fusionZStar ↥K₀) .PSL 2 p k :=
    GSThmB.OddQuot.lieModel_of_equiv (eZ.trans e).symm hBm
  have hc : center (↥K₀ ⧸ pPrimeCore 2 ↥K₀) ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective φ := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hbot]
      exact hker
    have hcard := Nat.card_congr (MulEquiv.ofBijective φ ⟨hinj, hφ⟩).toEquiv
    have hZ := OuterAutomorphisms.center_map_equiv (MulEquiv.ofBijective φ ⟨hinj, hφ⟩)
    rw [hbot, Subgroup.map_bot] at hZ
    rw [← hZ, card_bot] at hBZ
    exact absurd hBZ (by norm_num)
  exact (slTwo_of_lieModel hGA hK₀.2 hp hp2 hm hc).2.2

theorem image_slTwo {K₀ : Subgroup M} (hK₀ : IsTwoComponent K₀) {q : ℕ}
    (hsl : IsSLTwoOver q (↥K₀ ⧸ pPrimeCore 2 ↥K₀)) :
    IsComponent (K₀.map (barMk M)) ∧ IsSLTwoOver q ↥(K₀.map (barMk M)) := by
  have hc : IsComponent (K₀.map (barMk M)) :=
    isComponent_map_barMk ((L219.isTwoComponent_iff_twoComponents K₀).mp hK₀)
  refine ⟨hc, ?_⟩
  set f := (barMk M).subgroupMap K₀
  have hf : Function.Surjective f := (barMk M).subgroupMap_surjective K₀
  have hker : ¬ 2 ∣ Nat.card f.ker := by
    have hle : f.ker.map K₀.subtype ≤ pPrimeCore 2 M := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : barMk M (x : M) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hdvd : Nat.card f.ker ∣ Nat.card ↥(pPrimeCore 2 M) := by
      rw [← Subgroup.card_map_of_injective K₀.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    exact fun h2 => (Nat.prime_two.coprime_iff_not_dvd.mp pPrimeCore_coprime_card) (h2.trans hdvd)
  obtain ⟨e⟩ := GSThmB.OddQuot.nonempty_pPrimeCore_equiv_of_surjective f hf hker
  have hO : pPrimeCore 2 ↥(K₀.map (barMk M)) = ⊥ :=
    pPrimeCore_eq_bot_of_isSubnormal (pPrimeCore_quotient_pPrimeCore_eq_bot 2) hc.2
  have e' : ↥(K₀.map (barMk M)) ≃* ↥K₀ ⧸ pPrimeCore 2 ↥K₀ :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hO.symm)).trans
      e.symm
  exact isSLTwoOver_of_mulEquiv e' hsl

omit [Finite M] in
theorem mem_sup_of_mk_mem {K : Subgroup M} {x : M} (hx : barMk M x ∈ K.map (barMk M)) :
    x ∈ K ⊔ pPrimeCore 2 M := by
  obtain ⟨y, hy, hyx⟩ := hx
  have h1 : y⁻¹ * x ∈ pPrimeCore 2 M := by
    rw [← QuotientGroup.eq]
    exact hyx
  rw [show x = y * (y⁻¹ * x) by group]
  exact mul_mem (mem_sup_left hy) (mem_sup_right h1)

theorem mem_of_mk_mem {K : Subgroup M} (hK : IsTwoComponent K) {x : M}
    (hx : barMk M x ∈ K.map (barMk M)) (hxx : x * x = 1) : x ∈ K :=
  mem_of_mem_sup_of_pow_two_pow
    (L219.pPrimeCore_le_normalizer ((L219.isTwoComponent_iff_twoComponents K).mp hK))
    (Nat.coprime_two_left.mp pPrimeCore_coprime_card) (mem_sup_of_mk_mem hx)
    (n := 1) (by rw [pow_one, sq, hxx])

theorem not_mem_of_slTwo
    (hCI : GSLit.ClassicalInvolutionInput)
    {G : Type} [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hcat : ¬ Blueprint.Catalog G) {w : G} (hw2 : orderOf w = 2)
    {K₀ : Subgroup ↥(centralizer ({w} : Set G))} (hK₀ : IsTwoComponent K₀) {p k : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hsl : IsSLTwoOver (p ^ k) (↥K₀ ⧸ pPrimeCore 2 ↥K₀)) :
    (⟨w, mem_centralizer_singleton_iff.mpr rfl⟩ : ↥(centralizer ({w} : Set G))) ∉ K₀ := by
  intro hwK
  have hJ := isTwoComponentIn_map_subtype hK₀
  have hwJ : w ∈ K₀.map (centralizer ({w} : Set G)).subtype := ⟨_, hwK, rfl⟩
  let e := K₀.equivMapOfInjective _ (subtype_injective (centralizer ({w} : Set G)))
  exact T1.false_of_intrinsic_slTwo hCI hnonab hcat hw2 hJ hwJ hp hp2
    (isSLTwoOver_of_mulEquiv (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)).symm hsl)

theorem harris82Theorem3SLTwo_of
    (hCI : GSLit.ClassicalInvolutionInput) (hGA : TBLit.GriessMultipliersAllModels)
    (hT2 : Harris82Theorem2SLTwo) : Harris82Theorem3SLTwo := by
  intro G _ _ _ hnonab hK hcat W hW2 hW4 L p hp hp2 hL hM k hk h5 hsl w hw hw1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hwL, hwW⟩ := mem_inf.mp hw
  have hw2 : orderOf w = 2 := orderOf_eq_prime (by rw [sq]; exact hW2 w hwW) hw1
  obtain ⟨t, htW, htw⟩ : ∃ t ∈ W, t ∉ zpowers w := by
    by_contra h
    push Not at h
    have hle := Subgroup.card_le_of_le (show W ≤ zpowers w from fun x hx => h x hx)
    rw [hW4, Nat.card_zpowers, hw2] at hle
    omega
  obtain ⟨-, ht2, htM, hCW⟩ := L35.centralizer_eq_inf hW2 hW4 hwW hw1 htW htw
  have hL' : IsTwoComponentIn L (centralizer {w} ⊓ centralizer {t}) := hCW ▸ hL
  obtain ⟨K₀, hK₀, hKeq, hcases⟩ := exists_pumpup ht2 htM hL'
  rcases hcases with ⟨hfix, -⟩ | ⟨hne, hLeq⟩
  · rw [hKeq, hfix, sup_idem]
    exact isTwoComponentIn_map_subtype hK₀
  exfalso
  set t' : ↥(centralizer ({w} : Set G)) := ⟨t, htM⟩ with ht'def
  have ht'2 : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht2
  set K₁ := K₀.map (MulAut.conj t').toMonoidHom with hK₁def
  have hK₁ : IsTwoComponent K₁ := L219.isTwoComponent_map_conj hK₀ t'
  have hLM : L ≤ centralizer {w} := hL'.1.trans inf_le_left
  have hsl' : IsSLTwoOver (p ^ k) (↥(centralizerResidual (K₀ ⊔ K₁) t') ⧸
      pPrimeCore 2 ↥(centralizerResidual (K₀ ⊔ K₁) t')) := by
    rw [← hLeq]
    let e := subgroupOfEquivOfLe hLM
    exact isSLTwoOver_of_mulEquiv (QuotientGroup.congr _ _ e (pPrimeCore_map_iso 2 e)) hsl
  have hK₀sl := slTwo_of_diag hGA ht'2 hK₀ hne hp hp2 hk h5 hsl'
  let eK : ↥K₀ ≃* ↥K₁ := K₀.equivMapOfInjective _ (MulAut.conj t').injective
  have hK₁sl : IsSLTwoOver (p ^ k) (↥K₁ ⧸ pPrimeCore 2 ↥K₁) :=
    isSLTwoOver_of_mulEquiv (QuotientGroup.congr _ _ eK (pPrimeCore_map_iso 2 eK)).symm hK₀sl
  set w' : ↥(centralizer ({w} : Set G)) := ⟨w, mem_centralizer_singleton_iff.mpr rfl⟩ with hw'def
  have hwK₀ : w' ∉ K₀ := not_mem_of_slTwo hCI hnonab hcat hw2 hK₀ hp hp2 hK₀sl
  have hwK₁ : w' ∉ K₁ := not_mem_of_slTwo hCI hnonab hcat hw2 hK₁ hp hp2 hK₁sl
  have hw'w' : w' * w' = 1 := Subtype.ext (by
    change w * w = 1
    rw [← sq, ← hw2, pow_orderOf_eq_one])
  obtain ⟨hY₀c, hY₀sl⟩ := image_slTwo hK₀ hK₀sl
  obtain ⟨hY₁c, hY₁sl⟩ := image_slTwo hK₁ hK₁sl
  set Y₀ := K₀.map (barMk ↥(centralizer ({w} : Set G))) with hY₀def
  set Y₁ := K₁.map (barMk ↥(centralizer ({w} : Set G))) with hY₁def
  obtain ⟨hY₀q, hY₀Z, hY₀m, hY₀O⟩ := Lemma47.sl2_facts hp hp2 hk h5 hY₀sl
  obtain ⟨hY₁q, hY₁Z, hY₁m, hY₁O⟩ := Lemma47.sl2_facts hp hp2 hk h5 hY₁sl
  have hY₀₁ : Y₀ ≠ Y₁ := by
    intro hYeq
    apply hne
    have hle : K₁ ≤ K₀ := by
      refine L219.le_of_le_sup_of_odd hK₁.2.1 (Nat.coprime_two_left.mp pPrimeCore_coprime_card)
        (L219.pPrimeCore_le_normalizer ((L219.isTwoComponent_iff_twoComponents K₀).mp hK₀))
        fun x hx => mem_sup_of_mk_mem ?_
      rw [← hY₀def, hYeq]
      exact ⟨x, hx, rfl⟩
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [hK₁def, Subgroup.card_map_of_injective (MulAut.conj t').injective])
  have hcomm : ∀ a ∈ Y₀, ∀ b ∈ Y₁, a * b = b * a := by
    rcases LocalCores.distinct_components_commute hY₀c hY₁c with h | h
    · exact absurd h hY₀₁
    · intro a ha b hb
      have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h) ha
      exact (mem_centralizer_iff.mp h1 b hb).symm
  have hwY : barMk ↥(centralizer ({w} : Set G)) w' ∈ Y₀ ⊔ Y₁ := by
    have hwL' : w' ∈ L.subgroupOf (centralizer {w}) := hwL
    rw [hLeq] at hwL'
    have h1 : w' ∈ K₀ ⊔ K₁ := (centralizerResidual_le.trans inf_le_left) hwL'
    have h2 : barMk _ w' ∈ (K₀ ⊔ K₁).map (barMk ↥(centralizer ({w} : Set G))) :=
      ⟨w', h1, rfl⟩
    rwa [Subgroup.map_sup] at h2
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_commute hcomm hwY
  have hwc : ∀ y : barQ ↥(centralizer ({w} : Set G)), y * barMk _ w' = barMk _ w' * y := by
    intro y
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ y
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (mem_centralizer_singleton_iff.mp m.2)
  have haZ : ∀ y ∈ Y₀, y * a = a * y := by
    intro y hy
    have h1 := hwc y
    rw [← hab] at h1
    have h2 : y * a * b = a * y * b := by
      rw [mul_assoc, h1, mul_assoc, mul_assoc, hcomm y hy b hb]
    exact mul_right_cancel h2
  have hbZ : ∀ y ∈ Y₁, y * b = b * y := by
    intro y hy
    have h1 := hwc y
    rw [← hab] at h1
    have h2 : a * (y * b) = a * (b * y) :=
      calc a * (y * b) = a * y * b := (mul_assoc _ _ _).symm
        _ = y * a * b := by rw [hcomm a ha y hy]
        _ = y * (a * b) := mul_assoc _ _ _
        _ = a * b * y := h1
        _ = a * (b * y) := mul_assoc _ _ _
    exact mul_left_cancel h2
  have hcen : ∀ (Y : Subgroup (barQ ↥(centralizer ({w} : Set G))))
      {x : barQ ↥(centralizer ({w} : Set G))} (hx : x ∈ Y),
      (∀ y ∈ Y, y * x = x * y) → Nat.card ↥(center ↥Y) = 2 → x * x = 1 := by
    intro Y x hx hxc hZ
    have hxZ : (⟨x, hx⟩ : ↥Y) ∈ center ↥Y :=
      mem_center_iff.mpr fun y => Subtype.ext (hxc y y.2)
    have h1 : (⟨⟨x, hx⟩, hxZ⟩ : ↥(center ↥Y)) ^ Nat.card ↥(center ↥Y) = 1 := pow_card_eq_one'
    rw [hZ] at h1
    have h2 := congrArg (fun z : ↥(center ↥Y) => ((z : ↥Y) : barQ ↥(centralizer ({w} : Set G)))) h1
    simpa [sq] using h2
  have haa : a * a = 1 := hcen Y₀ ha haZ hY₀Z
  have hbb : b * b = 1 := hcen Y₁ hb hbZ hY₁Z
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [one_mul] at hab
    exact hwK₁ (mem_of_mk_mem hK₁ (hab ▸ hb) hw'w')
  have hb1 : b ≠ 1 := by
    rintro rfl
    rw [mul_one] at hab
    exact hwK₀ (mem_of_mk_mem hK₀ (hab ▸ ha) hw'w')
  obtain ⟨k₀, hk₀k₀, hk₀1, hk₀a⟩ :=
    exists_involution_lift (H := ↥(centralizer ({w} : Set G))) haa ha1
  have hk₀a' : barMk ↥(centralizer ({w} : Set G)) k₀ = a := hk₀a
  have hz₂b : barMk ↥(centralizer ({w} : Set G)) (w' * k₀) = b := by
    rw [map_mul, hk₀a', ← hab, mul_assoc, ← hcomm a ha b hb, ← mul_assoc, haa, one_mul]
  have hk₀2' : orderOf k₀ = 2 :=
    orderOf_eq_prime (by rw [sq]; exact hk₀k₀) hk₀1
  have hk₀2 : orderOf (k₀ : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hk₀2'
  have hwk₀ : (w' * k₀) * (w' * k₀) = 1 := by
    have hc : k₀ * w' = w' * k₀ :=
      Subtype.ext (mem_centralizer_singleton_iff.mp k₀.2)
    calc (w' * k₀) * (w' * k₀) = w' * (k₀ * w') * k₀ := by group
      _ = w' * (w' * k₀) * k₀ := by rw [hc]
      _ = (w' * w') * (k₀ * k₀) := by group
      _ = 1 := by rw [hw'w', hk₀k₀, one_mul]
  have hwk₀1 : w' * k₀ ≠ 1 := by
    intro h
    apply hb1
    rw [← hz₂b, h, map_one]
  have hwk₀2 : orderOf ((w' * k₀ : ↥(centralizer ({w} : Set G))) : G) = 2 := by
    rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq]; exact hwk₀) hwk₀1
  have hres : ∀ {Y C : Subgroup (barQ ↥(centralizer ({w} : Set G)))}, Y ≤ C →
      IsPComponent 2 Y → IsPComponent 2 (Y.subgroupOf C) := by
    intro Y C hYC h
    rw [← isTwoComponent_iff_isPComponent] at h ⊢
    exact ⟨h.1.subgroupOf, isTwoQuasisimple_of_mulEquiv (subgroupOfEquivOfLe hYC).symm h.2⟩
  have hpc : ∀ {Y : Subgroup (barQ ↥(centralizer ({w} : Set G)))}, IsComponent Y →
      IsPComponent 2 Y := fun hY => (isTwoComponent_iff_isPComponent _).mp
    ((isTwoComponent_iff_isComponent (pPrimeCore_quotient_pPrimeCore_eq_bot 2) _).mpr hY)
  have hY₀le : Y₀ ≤ centralizer {(QuotientGroup.mk ⟨(k₀ : G), k₀.2⟩ : MBar w)} := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    change y * barMk _ k₀ = barMk _ k₀ * y
    rw [hk₀a']
    exact haZ y hy
  have hY₁le : Y₁ ≤ centralizer
      {(QuotientGroup.mk ⟨((w' * k₀ : ↥(centralizer ({w} : Set G))) : G), (w' * k₀).2⟩ :
        MBar w)} := by
    intro y hy
    rw [mem_centralizer_singleton_iff]
    change y * barMk _ (w' * k₀) = barMk _ (w' * k₀) * y
    rw [hz₂b]
    exact hbZ y hy
  obtain ⟨J₁, hJ₁le, hJ₁p, hk₀J₁, -, g₁, hg₁, hg₁k⟩ := Lemma47.exists_lift_two_component k₀.2
    hk₀2 hY₀le (hres hY₀le (hpc hY₀c)) (by
      change barMk _ k₀ ∈ Y₀
      rw [hk₀a']
      exact ha)
  obtain ⟨J₂, hJ₂le, hJ₂p, hz₂J₂, -, g₂, hg₂, hg₂k⟩ := Lemma47.exists_lift_two_component
    (w' * k₀).2 hwk₀2 hY₁le (hres hY₁le (hpc hY₁c)) (by
      change barMk _ (w' * k₀) ∈ Y₁
      rw [hz₂b]
      exact hb)
  have hGO := TBLit.GriessMultipliersOdd.of_allModels hGA
  have hJ₁c := (isTwoComponentIn_iff hJ₁le).mpr hJ₁p
  have hJ₂c := (isTwoComponentIn_iff hJ₂le).mpr hJ₂p
  have hMJ₁ : IsMTypeSchur p ↥J₁ :=
    isMTypeSchur_of_surjective hGO hp hp2 g₁ hg₁ hg₁k hJ₁c.2.2.1 hY₀q hY₀O hY₀Z hY₀m
  have hMJ₂ : IsMTypeSchur p ↥J₂ :=
    isMTypeSchur_of_surjective hGO hp hp2 g₂ hg₂ hg₂k hJ₂c.2.2.1 hY₁q hY₁O hY₁Z hY₁m
  obtain ⟨eZ₁⟩ := GSThmB.OddQuot.nonempty_fusionZStar_equiv_of_surjective g₁ hg₁ hg₁k
  have hmJ₁ : Blueprint.LieModel (↥J₁ ⧸ Open.fusionZStar ↥J₁) .PSL 2 p k :=
    GSThmB.OddQuot.lieModel_of_equiv (eZ₁.trans (QuotientGroup.quotientMulEquivOfEq
      (fusionZStar_eq_center_of_pPrimeCore_eq_bot hY₀O))).symm hY₀m
  have hk₀w : (k₀ : G) ≠ w := by
    intro h
    apply hb1
    have h1 : k₀ = w' := Subtype.ext h
    rw [← hz₂b, h1, hw'w', map_one]
  have hck : w * (k₀ : G) = (k₀ : G) * w := (mem_centralizer_singleton_iff.mp k₀.2).symm
  have hV := Lemma47.fourGroup_closure_pair hw2 hk₀2 hk₀w hck
  have hCV := Lemma47.centralizer_closure_pair w (k₀ : G)
  have hk₀V : (k₀ : G) ∈ (closure {w, (k₀ : G)} : Subgroup G) :=
    subset_closure (Set.mem_insert_of_mem _ rfl)
  have hwkV : w * (k₀ : G) ∈ (closure {w, (k₀ : G)} : Subgroup G) :=
    mul_mem (subset_closure (Set.mem_insert _ _)) hk₀V
  have hk₀ne : (k₀ : G) ≠ 1 := fun h => hk₀1 (Subtype.ext h)
  have hwkne : w * (k₀ : G) ≠ 1 := fun h => hk₀w (by
    rw [eq_inv_of_mul_eq_one_right h, inv_eq_of_mul_eq_one_right (hW2 w hwW)])
  have hkwk : (k₀ : G) ≠ w * (k₀ : G) := fun h => hw1 (by
    have h1 := h.symm
    rwa [mul_eq_right] at h1)
  have hJ₁V : IsTwoComponentIn J₁ (centralizer ((closure {w, (k₀ : G)} : Subgroup G) : Set G)) :=
    hCV ▸ hJ₁c
  have hJ₂V : IsTwoComponentIn J₂ (centralizer ((closure {w, (k₀ : G)} : Subgroup G) : Set G)) := by
    rw [hCV, ← centralizer_inf_mul]
    exact hJ₂c
  exact hcat (hT2 G hnonab hK _ hV.1 hV.2 (k₀ : G) hk₀V (w * (k₀ : G)) hwkV hk₀ne hwkne hkwk J₁ J₂
    hJ₁V hJ₂V hk₀J₁ hz₂J₂ p hp hp2 hMJ₁ hMJ₂ ⟨k, hmJ₁⟩)

end CFSG.ComponentClassification.HarrisLit.T23
