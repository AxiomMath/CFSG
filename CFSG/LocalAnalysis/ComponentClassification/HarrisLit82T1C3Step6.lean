module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Step4
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1C3Sylow

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit.T1

open CFSG Subgroup Assembly.LowTwoRank CFSG.ComponentClassification.UnbalancedLayer
open CFSG.LieType.Universal.Spin CliffordAlgebra CFSG.ABGLocalTools
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem C3Config.conj {z : G} {L : Subgroup G} {p f : ℕ} (h : C3Config G z L p f) (g : G) :
    C3Config G (g * z * g⁻¹) (L.map (MulAut.conj g).toMonoidHom) p f := by
  have hmap : (centralizer ({z} : Set G)).map (MulAut.conj g).toMonoidHom =
      centralizer {g * z * g⁻¹} := by
    rw [map_centralizer_singleton_mulEquiv, MulAut.conj_apply]
  let eg : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    L.equivMapOfInjective _ (MulAut.conj g).injective
  exact ⟨h.simple, h.nonab, h.kProper, h.notCat,
    by rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]; exact h.hz,
    hmap ▸ L35.isTwoComponentIn_map_of_injective _ (MulAut.conj g).injective h.hL,
    ⟨z, h.hzL, rfl⟩, h.hp, h.hp2, h.h5,
    isCoverOf_of_mulEquiv (QuotientGroup.congr _ _ eg (pPrimeCore_map_iso 2 eg)) h.hcov,
    T23.isMTypeSchur_of_mulEquiv eg h.hM⟩

omit [Finite G] in
theorem conj_mem_coreActionKernel {L : Subgroup G} {a : G} (ha : a ∈ coreActionKernel L)
    (g : G) : g * a * g⁻¹ ∈ coreActionKernel (L.map (MulAut.conj g).toMonoidHom) := by
  obtain ⟨haN, ha'⟩ := mem_coreActionKernel.mp ha
  let e : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) :=
    L.equivMapOfInjective _ (MulAut.conj g).injective
  have hO : ((pPrimeCore 2 ↥L).map L.subtype).map (MulAut.conj g).toMonoidHom =
      (pPrimeCore 2 ↥(L.map (MulAut.conj g).toMonoidHom)).map
        (L.map (MulAut.conj g).toMonoidHom).subtype := by
    rw [← pPrimeCore_map_iso 2 e, map_map, map_map]
    congr 1
  refine mem_coreActionKernel.mpr ⟨?_, fun j hj => ?_⟩
  · rw [mem_normalizer_iff]
    intro x
    rw [mem_map_equiv, mem_map_equiv, MulAut.conj_symm_apply, MulAut.conj_symm_apply]
    have h1 : g⁻¹ * (g * a * g⁻¹ * x * (g * a * g⁻¹)⁻¹) * g = a * (g⁻¹ * x * g) * a⁻¹ := by
      group
    rw [h1]
    exact mem_normalizer_iff.mp haN _
  · obtain ⟨j₀, hj₀, rfl⟩ := hj
    rw [← hO]
    refine ⟨_, ha' j₀ hj₀, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem eq_of_mk_mem_center_of_le {X : Subgroup G} {z : G} (hXz : X ≤ centralizer {z})
    (hzX : z ∈ X) (hz : orderOf z = 2) (hZ2 : Nat.card ↥(center (Bar X)) = 2) {u : G}
    (huX : u ∈ X) (hu : orderOf u = 2)
    (huZ : (QuotientGroup.mk (⟨u, huX⟩ : ↥X) : Bar X) ∈ center (Bar X)) : u = z := by
  have hOodd := odd_card_pPrimeCore_two ↥X
  have hzc := mem_center_of_le_centralizer hXz hzX
  have hz' : orderOf (⟨z, hzX⟩ : ↥X) = 2 := by rw [Subgroup.orderOf_mk]; exact hz
  have hu' : orderOf (⟨u, huX⟩ : ↥X) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have heq := T23.eq_of_ne_one_of_card_two hZ2 (a := ⟨_, huZ⟩)
    (b := ⟨_, mk_mem_center_of_mem_center hzc⟩)
    (fun h1 => mk_ne_one_of_orderOf_two hu' (congrArg Subtype.val h1))
    (fun h1 => mk_ne_one_of_orderOf_two hz' (congrArg Subtype.val h1))
  have heq' : (QuotientGroup.mk (⟨u, huX⟩ : ↥X) : Bar X) = QuotientGroup.mk ⟨z, hzX⟩ :=
    congrArg Subtype.val heq
  rw [QuotientGroup.eq] at heq'
  have huu : (⟨u, huX⟩ : ↥X) * ⟨u, huX⟩ = 1 := by rw [← sq, ← hu', pow_orderOf_eq_one]
  have hzz : (⟨z, hzX⟩ : ↥X) * ⟨z, hzX⟩ = 1 := by rw [← sq, ← hz', pow_orderOf_eq_one]
  obtain ⟨c, -, hc⟩ := exists_conj_of_inv_mul_mem hOodd huu hzz heq'
  have h1 : (⟨u, huX⟩ : ↥X) = ⟨z, hzX⟩ := by
    calc (⟨u, huX⟩ : ↥X) = c⁻¹ * (c * ⟨u, huX⟩ * c⁻¹) * c := by group
      _ = c⁻¹ * ⟨z, hzX⟩ * c := by rw [hc]
      _ = ⟨z, hzX⟩ := by rw [mul_assoc, ← mem_center_iff.mp hzc c, inv_mul_cancel_left]
  exact congrArg Subtype.val h1

theorem mem_pPrimeCore_of_le {X K : Subgroup G} (hXK : X ≤ K) {x : G} (hxX : x ∈ X)
    (hxK : x ∈ (pPrimeCore 2 ↥K).map K.subtype) : (⟨x, hxX⟩ : ↥X) ∈ pPrimeCore 2 ↥X := by
  set OK := (pPrimeCore 2 ↥K).map K.subtype with hOK
  have hN : (OK.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hgN : (g : G) ∈ normalizer (OK : Set G) :=
      UnbalancedGS.normalizer_le_normalizer_map_of_characteristic K (pPrimeCore 2 ↥K)
        (le_normalizer (hXK g.2))
    exact (mem_normalizer_iff.mp hgN n).mp hn
  have hdvd : Nat.card ↥(OK.subgroupOf X) ∣ Nat.card ↥(pPrimeCore 2 ↥K) := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, subgroupOf_map_subtype,
      ← Subgroup.card_map_of_injective K.subtype_injective]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hcop := Nat.Coprime.coprime_dvd_right hdvd (pPrimeCore_coprime_card (p := 2) (G := ↥K))
  exact le_sSup (s := {N : Subgroup ↥X | N.Normal ∧ Nat.Coprime 2 (Nat.card N)}) ⟨hN, hcop⟩
    (show (⟨x, hxX⟩ : ↥X) ∈ OK.subgroupOf X from hxK)

omit [Finite G] in
theorem mk_mem_center_of_mem_coreActionKernel {L : Subgroup G} {u : G} (huL : u ∈ L)
    (hu : u ∈ coreActionKernel L) :
    (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : Bar L) ∈ center (Bar L) := by
  rw [mem_center_iff]
  intro g
  obtain ⟨⟨j, hj⟩, rfl⟩ := QuotientGroup.mk_surjective g
  obtain ⟨o, ho, hoeq⟩ := (mem_coreActionKernel.mp hu).2 j hj
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have hoeq' : (o : G) = j⁻¹ * u⁻¹ * j * u := hoeq
  have h1 : (⟨j, hj⟩ * ⟨u, huL⟩ : ↥L)⁻¹ * (⟨u, huL⟩ * ⟨j, hj⟩) = o⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, hoeq']
    group
  rw [h1]
  exact inv_mem ho

theorem eq_of_map_bar_eq {Y : Type} [Group Y] [Finite Y] {t : Y} (ht : orderOf t = 2)
    {J J' : Subgroup Y} (hJ : IsTwoComponentIn J (centralizer {t}))
    (hJ' : IsTwoComponentIn J' (centralizer {t}))
    (heq : J.map (QuotientGroup.mk' (pPrimeCore 2 Y)) =
      J'.map (QuotientGroup.mk' (pPrimeCore 2 Y))) :
    J = J' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (pPrimeCore 2 Y)
  set C := centralizer ({t} : Set Y)
  have htt : t * t = 1 := by rw [← sq, ← ht, pow_orderOf_eq_one]
  have hodd := odd_card_pPrimeCore_two Y
  have hCmap : C.map π = centralizer {(QuotientGroup.mk t : Y ⧸ pPrimeCore 2 Y)} :=
    map_centralizer_eq hodd htt
  let φ : ↥C →* ↥(centralizer ({(QuotientGroup.mk t : Y ⧸ pPrimeCore 2 Y)} :
      Set (Y ⧸ pPrimeCore 2 Y))) :=
    (π.comp C.subtype).codRestrict _ (fun x => hCmap ▸ mem_map_of_mem π x.2)
  have hφs : Function.Surjective φ := by
    rintro ⟨y, hy⟩
    rw [← hCmap] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨⟨x, hx⟩, rfl⟩
  have hφk : ¬ 2 ∣ Nat.card φ.ker := by
    have hle : φ.ker.map C.subtype ≤ pPrimeCore 2 Y := by
      rintro _ ⟨x, hx, rfl⟩
      have hx' : π (x : Y) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
      rwa [← MonoidHom.mem_ker, QuotientGroup.ker_mk'] at hx'
    have hc : Nat.card φ.ker ∣ Nat.card (pPrimeCore 2 Y) := by
      rw [← Subgroup.card_map_of_injective C.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    intro h2
    exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (h2.trans hc))
  obtain ⟨hbij, -, -⟩ :=
    CatalogueBPrimeJoin.prime_complement_quotient_p_component_bijection φ hφs hφk
  have hJp : IsPComponent 2 (J.subgroupOf C) := (isTwoComponentIn_iff hJ.1).mp hJ
  have hJ'p : IsPComponent 2 (J'.subgroupOf C) := (isTwoComponentIn_iff hJ'.1).mp hJ'
  have hmap : ∀ {K : Subgroup Y}, K ≤ C → (K.subgroupOf C).map φ =
      (K.map π).subgroupOf (centralizer {(QuotientGroup.mk t : Y ⧸ pPrimeCore 2 Y)}) := by
    intro K hK
    ext ⟨y, hy⟩
    constructor
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, congrArg Subtype.val hxy⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hK hx⟩, hx, rfl⟩
  have h1 := hbij.injOn hJp hJ'p (by rw [hmap hJ.1, hmap hJ'.1, heq])
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hJ.1, inf_eq_left.mpr hJ'.1] at h1
  exact h1

variable {z : G} {L : Subgroup G} {p f : ℕ}

theorem C3Config.eq_of_mem_twoComponent (hI : C3Inputs) (h : C3Config G z L p f) {u : G}
    (huL : u ∈ L) (hu : orderOf u = 2)
    (huZ : (QuotientGroup.mk (⟨u, huL⟩ : ↥L) : Bar L) ∉ center (Bar L)) {K K' : Subgroup G}
    (hK : IsTwoComponentIn K (centralizer {z} ⊓ centralizer {u}))
    (hK' : IsTwoComponentIn K' (centralizer {z} ⊓ centralizer {u})) (huK : u ∈ K)
    (huK' : u ∈ K') : K = K' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huz : u ∈ centralizer ({z} : Set G) := h.hL.1 huL
  have hle : ∀ {K : Subgroup G}, IsTwoComponentIn K (centralizer {z} ⊓ centralizer {u}) →
      u ∈ K → K ≤ L := by
    intro K hK huK
    rcases lemma221 hu huz hK huK h.hL with h1 | h1
    · exact h1
    · exact absurd (mk_mem_center_of_mem_coreActionKernel huL (h1 huK)) huZ
  have hKL := hle hK huK
  have hK'L := hle hK' huK'
  have hsub : ∀ {K : Subgroup G}, IsTwoComponentIn K (centralizer {z} ⊓ centralizer {u}) →
      K ≤ L → IsTwoComponentIn K (L ⊓ centralizer {u}) := fun hK hKL =>
    ⟨le_inf hKL (hK.1.trans inf_le_right),
      L219.isSubnormal_subgroupOf_of_le (inf_le_inf_right _ h.hL.1) hK.2.1, hK.2.2⟩
  have hu' : orderOf (⟨u, huL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact hu
  have hKb := isTwoComponentIn_subgroupOf_inf huL (hsub hK hKL)
  have hK'b := isTwoComponentIn_subgroupOf_inf huL (hsub hK' hK'L)
  obtain ⟨hJ, -⟩ := isTwoComponentIn_map_bar hu' hKb
  obtain ⟨hJ', -⟩ := isTwoComponentIn_map_bar hu' hK'b
  have hzc := mem_center_of_le_centralizer h.hL.1 h.hzL
  have hz' : orderOf (⟨z, h.hzL⟩ : ↥L) = 2 := by rw [Subgroup.orderOf_mk]; exact h.hz
  obtain ⟨-, h410t⟩ := hI.l410 (Bar L) p f h.hp h.hp2 h.h5 h.hcov _
    (mk_mem_center_of_mem_center hzc) (mk_ne_one_of_orderOf_two hz')
  obtain ⟨-, huniq, -⟩ := h410t _ (orderOf_mk_eq_two (odd_card_pPrimeCore_two ↥L) hu') huZ
  have hbar := huniq _ _ hJ hJ' _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
    ⟨⟨u, huL⟩, huK, rfl⟩ ⟨⟨u, huL⟩, huK', rfl⟩
  have heq := eq_of_map_bar_eq hu' hKb hK'b hbar
  rw [Subgroup.subgroupOf_inj, inf_eq_left.mpr hKL, inf_eq_left.mpr hK'L] at heq
  exact heq

omit [Finite G] in
theorem orderOf_mul_of_commute {z z₁ : G} (hz : orderOf z = 2) (hz₁ : orderOf z₁ = 2)
    (hc : z * z₁ = z₁ * z) (hne : z₁ ≠ z) : orderOf (z * z₁) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hz2 : z ^ 2 = 1 := hz ▸ pow_orderOf_eq_one z
  have hz₁2 : z₁ ^ 2 = 1 := hz₁ ▸ pow_orderOf_eq_one z₁
  refine orderOf_eq_prime ?_ ?_
  · rw [(show Commute z z₁ from hc).mul_pow, hz2, hz₁2, one_mul]
  · intro h1
    apply hne
    have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right (by rw [← sq, hz2])
    rw [← hzi]
    exact eq_inv_of_mul_eq_one_right h1

section Certified


theorem C3Config.exists_z₁ (hI : C3Inputs) (h : C3Config G z L p f) {S : Subgroup G}
    (hS : IsSylowOf 2 S (centralizer {z})) :
    ∃ z₁ : G, ∃ hz₁L : z₁ ∈ L, z₁ ∈ S ∧ orderOf z₁ = 2 ∧
      (QuotientGroup.mk (⟨z₁, hz₁L⟩ : ↥L) : Bar L) ∉ center (Bar L) ∧
      IsSylowOf 2 (S ⊓ centralizer {z₁}) (centralizer {z} ⊓ centralizer {z₁}) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, _, _, hK, -, hp, hp2, ⟨e₁⟩⟩ := nonempty_mulEquiv_spinOdd h.h5 h.hcov
  obtain ⟨-, t₀, -, -, -, -, -, ht₀2, ht₀Z, -⟩ := spinSeven_lemma410c (K := K) hp hp2 hK h.h5
  have htb2 : orderOf (e₁.symm t₀) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht₀2
  obtain ⟨k, hk2, hk1, hkmk⟩ := T23.exists_involution_lift (H := ↥L) (a := e₁.symm t₀)
    (by have h1 := pow_orderOf_eq_one (e₁.symm t₀); rwa [htb2, sq] at h1)
    (fun h1 => by rw [h1, orderOf_one] at htb2; exact absurd htb2 (by norm_num))
  set t : G := (k : G) with ht
  have htL : t ∈ L := k.2
  have hto : orderOf t = 2 := by
    rw [ht, Subgroup.orderOf_coe]
    exact orderOf_eq_prime (by rw [sq, hk2]) hk1
  have htZ : (QuotientGroup.mk (⟨t, htL⟩ : ↥L) : Bar L) ∉ center (Bar L) := by
    have hkt : (⟨t, htL⟩ : ↥L) = k := rfl
    rw [hkt, hkmk]
    intro hc
    apply ht₀Z
    have h1 := (mem_center_mulEquiv_iff e₁ (e₁.symm t₀)).mpr hc
    rwa [MulEquiv.apply_symm_apply] at h1
  have htz : t ∈ centralizer ({z} : Set G) := h.hL.1 htL
  have htt : t ∈ centralizer ({t} : Set G) := mem_centralizer_singleton_iff.mpr rfl
  have httsq : t ^ 2 ^ 1 = 1 := by rw [pow_one, ← hto, pow_orderOf_eq_one]
  obtain ⟨T₀, hT₀, htT₀⟩ := exists_isSylowOf_le
    (zpowers_le.mpr (mem_inf.mpr ⟨htz, htt⟩) : zpowers t ≤ centralizer {z} ⊓ centralizer {t})
    (isPGroup_zpowers_of_pow httsq)
  obtain ⟨S₀, hS₀, hT₀S₀⟩ := exists_isSylowOf_le (hT₀.le.trans inf_le_left) hT₀.isPGroup
  obtain ⟨k₀, hk₀, hk₀S⟩ := hS.exists_mem_conj hS₀
  set z₁ := k₀⁻¹ * t * k₀ with hz₁
  have hLn := h.normal hI
  have hz₁L : z₁ ∈ L := by
    have h1 := (normal_subgroupOf_iff h.hL.1).mp hLn t k₀⁻¹ htL (inv_mem hk₀)
    rwa [inv_inv] at h1
  have hz₁S : z₁ ∈ S := (hk₀S t).mp (hT₀S₀ (htT₀ (mem_zpowers t)))
  have hz₁o : orderOf z₁ = 2 := by
    rw [hz₁, show k₀⁻¹ * t * k₀ = MulAut.conj k₀⁻¹ t by rw [MulAut.conj_apply, inv_inv],
      MulEquiv.orderOf_eq]
    exact hto
  have hk₀c : k₀ * z = z * k₀ := mem_centralizer_singleton_iff.mp hk₀
  have hk₀z : k₀⁻¹ * z * k₀ = z := by
    calc k₀⁻¹ * z * k₀ = k₀⁻¹ * (k₀ * z) := by rw [mul_assoc, hk₀c]
      _ = z := by group
  have hk₀z' : k₀ * z * k₀⁻¹ = z := by rw [hk₀c, mul_inv_cancel_right]
  have hz₁Z : (QuotientGroup.mk (⟨z₁, hz₁L⟩ : ↥L) : Bar L) ∉ center (Bar L) := by
    intro hc
    have h1 := h.eq_of_mk_mem_center hz₁L hz₁o hc
    have h2 : t = z := by
      calc t = k₀ * z₁ * k₀⁻¹ := by rw [hz₁]; group
        _ = k₀ * z * k₀⁻¹ := by rw [h1]
        _ = z := hk₀z'
    apply htZ
    have h3 : (⟨t, htL⟩ : ↥L) = ⟨z, h.hzL⟩ := Subtype.ext h2
    rw [h3]
    exact mk_mem_center_of_mem_center (mem_center_of_le_centralizer h.hL.1 h.hzL)
  refine ⟨z₁, hz₁L, hz₁S, hz₁o, hz₁Z, ?_⟩
  set P₁ := T₀.map (MulAut.conj k₀⁻¹).toMonoidHom with hP₁
  have hCmap : (centralizer ({z} : Set G) ⊓ centralizer {t}).map (MulAut.conj k₀⁻¹).toMonoidHom =
      centralizer {z} ⊓ centralizer {z₁} := by
    rw [Subgroup.map_inf _ _ _ (MulAut.conj k₀⁻¹).injective, map_centralizer_singleton_mulEquiv,
      map_centralizer_singleton_mulEquiv, MulAut.conj_apply, MulAut.conj_apply, inv_inv, hk₀z]
  have hP₁le : P₁ ≤ S ⊓ centralizer {z₁} := by
    rintro _ ⟨x, hx, rfl⟩
    refine mem_inf.mpr ⟨?_, ?_⟩
    · have h1 := (hk₀S x).mp (hT₀S₀ hx)
      simpa [MulAut.conj_apply] using h1
    · have h1 : (MulAut.conj k₀⁻¹).toMonoidHom x ∈
          (centralizer ({z} : Set G) ⊓ centralizer {t}).map (MulAut.conj k₀⁻¹).toMonoidHom :=
        mem_map_of_mem _ (hT₀.le hx)
      rw [hCmap] at h1
      exact (mem_inf.mp h1).2
  have hP₁syl : IsSylowOf 2 P₁ (centralizer {z} ⊓ centralizer {z₁}) := by
    refine isSylowOf_of_card ?_ ?_
    · rw [← hCmap]
      exact map_mono hT₀.le
    · rw [hP₁, card_map_of_injective (MulAut.conj k₀⁻¹).injective, hT₀.card_eq, ← hCmap,
        card_map_of_injective (MulAut.conj k₀⁻¹).injective]
  have heq := hP₁syl.eq_of_le hP₁le (inf_le_inf_right _ hS.le) (hS.isPGroup.to_inf_left)
  rw [heq]
  exact hP₁syl

end Certified

end CFSG.ComponentClassification.HarrisLit.T1
