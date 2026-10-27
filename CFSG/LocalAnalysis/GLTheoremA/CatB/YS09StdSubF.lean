module

public import CFSG.LocalAnalysis.GLTheoremA.CatB.Lift
public import CFSG.LocalAnalysis.GLTheoremA.P55.I336.Q8
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Blueprint.SourceClassicalTransportLinear
public import CFSG.CharacterTheory.Semidihedral.CyclicPairFrattini
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import Certificates.Data.ExceptionalSL3

public section

namespace CFSG.LocalAnalysis.GLTheoremA.CatB

open Subgroup CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremB

theorem stdSub_of_model {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple ↥K) {M : Type} [Group M] [Finite M]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* M) (hZ : Nat.card (Subgroup.center ↥K) ∣ 2)
    {EM FM TM : Subgroup M} {gM : M}
    (hEel : IsElemAbelian 3 EM) (hEc : Nat.card EM = 3 ^ 3) (hFE : FM ≤ EM)
    (hFc : Nat.card FM = 3 ^ 2) (hgE : gM ∈ EM) (hgF : gM ∉ FM)
    (hT2 : IsPGroup 2 TM) (hFN : ∀ f ∈ FM, ∀ t ∈ TM, f * t * f⁻¹ ∈ TM)
    (hTc : ∃ t ∈ TM, ∃ f ∈ FM, t * f ≠ f * t)
    (hTcard : Nat.card (Subgroup.center ↥K) * Nat.card TM ≠ 8) :
    ∃ F T E : Subgroup G, F ≤ K ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 2 ∧ T ≤ K ∧
      IsPGroup 2 T ∧ F ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, F⁆ : Subgroup G) ≠ ⊥ ∧
      IsEmpty (T ≃* QuaternionGroup 2) ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K ∧
      (∃ g ∈ K ⊓ Subgroup.centralizer (F : Set G), g ^ 3 = 1 ∧ g ∉ F) ∧
      E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
      (∀ g ∈ K ⊓ Subgroup.centralizer (K : Set G), g ^ 3 = 1 → g = 1) := by
  classical
  set Z := Subgroup.center ↥K with hZdef
  let π : ↥K →* M := e.toMonoidHom.comp (QuotientGroup.mk' Z)
  have hπs : Function.Surjective π := e.surjective.comp (QuotientGroup.mk'_surjective Z)
  have hker : π.ker = Z := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' Z x) = 1 ↔ x ∈ Z
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hk3 : ¬ 3 ∣ Nat.card π.ker := by
    rw [hker]
    intro h
    have := Nat.dvd_trans h hZ
    norm_num at this
  have hZexp : ∀ z ∈ Z, z ^ 2 = 1 := by
    intro z hz
    have h1 : orderOf z ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hz
    exact orderOf_dvd_iff_pow_eq_one.1 (h1.trans hZ)
  have hZtriv : ∀ z ∈ Z, z ^ 3 = 1 → z = 1 := by
    intro z hz h3
    have h1 : orderOf z ∣ Nat.card Z := Subgroup.orderOf_dvd_natCard Z hz
    have h2 : orderOf z ∣ 3 := orderOf_dvd_iff_pow_eq_one.2 h3
    have h3' : orderOf z ∣ 2 := h1.trans hZ
    have : orderOf z ∣ Nat.gcd 2 3 := Nat.dvd_gcd h3' h2
    rw [show Nat.gcd 2 3 = 1 by norm_num, Nat.dvd_one, orderOf_eq_one_iff] at this
    exact this
  obtain ⟨WE, hWEp, hWEmap, hWEinj⟩ := exists_pSubgroup_lift Nat.prime_three π hk3
    (isPGroup_of_isElemAbelian hEel) (by rw [MonoidHom.range_eq_top.2 hπs]; exact le_top)
  obtain ⟨hWEel, hWEcard⟩ := map_subtype_isElemAbelian_card π hWEmap hWEinj hEel
  have hWEcomm : ∀ x y : WE, x * y = y * x := by
    intro x y
    apply hWEinj
    have hx : π (x : ↥K) ∈ EM := hWEmap ▸ Subgroup.mem_map_of_mem π x.2
    have hy : π (y : ↥K) ∈ EM := hWEmap ▸ Subgroup.mem_map_of_mem π y.2
    have hc := congrArg Subtype.val (hEel.1.is_comm.comm ⟨π x, hx⟩ ⟨π y, hy⟩)
    simp only [Function.comp_apply, Subgroup.coe_subtype, map_mul]
    exact hc
  have hWEexp : ∀ x : WE, x ^ 3 = 1 := by
    intro x
    apply hWEinj
    have hx : π (x : ↥K) ∈ EM := hWEmap ▸ Subgroup.mem_map_of_mem π x.2
    simp only [Function.comp_apply, Subgroup.coe_subtype, map_pow, map_one]
    exact hEel.2 _ hx
  have hF'WE : WE ⊓ FM.comap π ≤ WE := inf_le_left
  have hF'π : (WE ⊓ FM.comap π).map π = FM := by
    ext f
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_comap.1 hx.2
    · intro hf
      have hfE : f ∈ WE.map π := hWEmap ▸ hFE hf
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hfE
      exact Subgroup.mem_map.2 ⟨w, ⟨hw, Subgroup.mem_comap.2 hf⟩, rfl⟩
  have hF'card : Nat.card (WE ⊓ FM.comap π : Subgroup ↥K) = 3 ^ 2 := by
    have hinj : Function.Injective (π.comp (WE ⊓ FM.comap π : Subgroup ↥K).subtype) := by
      intro x y hxy
      have h1 : (⟨x.1, hF'WE x.2⟩ : WE) = ⟨y.1, hF'WE y.2⟩ := hWEinj hxy
      have h2 := congrArg (fun z : WE => (z : ↥K)) h1
      exact Subtype.ext h2
    rw [card_eq_of_injective_comp_subtype π hinj, hF'π, hFc]
  have hFcard : Nat.card ((WE ⊓ FM.comap π).map K.subtype) = 3 ^ 2 := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hF'card]
  have hFel : IsElemAbelian 3 ((WE ⊓ FM.comap π).map K.subtype) :=
    isElemAbelian_mono hWEel (Subgroup.map_mono hF'WE)
  have hFK : (WE ⊓ FM.comap π).map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hEK : WE.map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hZπ : ∀ z ∈ Z, π z = 1 := fun z hz => by
    rw [← hker] at hz
    exact MonoidHom.mem_ker.1 hz
  have hT'2 : ∀ x ∈ TM.comap π, ∃ k : ℕ, x ^ 2 ^ k = 1 := by
    intro x hx
    obtain ⟨k, hk⟩ := hT2 ⟨π x, hx⟩
    refine ⟨k + 1, ?_⟩
    have h1 : π (x ^ 2 ^ k) = 1 := by
      rw [map_pow]
      have := congrArg Subtype.val hk
      simpa using this
    have h2 : x ^ 2 ^ k ∈ Z := by
      rw [← hker]
      exact MonoidHom.mem_ker.2 h1
    rw [pow_succ, pow_mul]
    exact hZexp _ h2
  have hT'card : Nat.card (TM.comap π : Subgroup ↥K) = Nat.card Z * Nat.card TM := by
    let f : ↥(TM.comap π) →* M := π.comp (TM.comap π).subtype
    have hrange : f.range = TM := by
      ext m
      constructor
      · rintro ⟨x, rfl⟩
        exact x.2
      · intro hm
        obtain ⟨x, hx⟩ := hπs m
        exact ⟨⟨x, Subgroup.mem_comap.2 (hx ▸ hm)⟩, hx⟩
    have hkerf : Nat.card f.ker = Nat.card Z := by
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1.1, by rw [← hker]; exact MonoidHom.mem_ker.2 x.2⟩
          invFun := fun z => ⟨⟨z.1, Subgroup.mem_comap.2 (by rw [hZπ z.1 z.2]; exact one_mem TM)⟩,
            MonoidHom.mem_ker.2 (hZπ z.1 z.2)⟩
          left_inv := fun x => Subtype.ext (Subtype.ext rfl)
          right_inv := fun z => Subtype.ext rfl }
    have h := Subgroup.card_ker_mul_card_range f
    rw [hkerf, hrange] at h
    exact h.symm
  have hTcard' : Nat.card ((TM.comap π).map K.subtype) = Nat.card Z * Nat.card TM := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hT'card]
  have hTK : (TM.comap π).map K.subtype ≤ K := Subgroup.map_subtype_le _
  have hTp : IsPGroup 2 ((TM.comap π).map K.subtype) := by
    intro g
    obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
    obtain ⟨k, hk⟩ := hT'2 x hx
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (g : G) ^ 2 ^ k = 1 := by
      rw [← hxg, ← map_pow, hk, map_one]
    simpa using h1
  have hempty : IsEmpty ((TM.comap π).map K.subtype ≃* QuaternionGroup 2) := by
    refine ⟨fun φ => hTcard ?_⟩
    have h8 := CFSG.LocalAnalysis.GLTheoremA.P55.I336.card_eq_eight_of_q8 φ
    rw [hTcard'] at h8
    exact h8
  have hconj : ∀ f ∈ (WE ⊓ FM.comap π).map K.subtype, ∀ t ∈ (TM.comap π).map K.subtype,
      f * t * f⁻¹ ∈ (TM.comap π).map K.subtype := by
    intro f hf t ht
    obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.1 hf
    obtain ⟨t', ht', rfl⟩ := Subgroup.mem_map.1 ht
    refine Subgroup.mem_map.2 ⟨f' * t' * f'⁻¹, ?_, by simp⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hFN (π f') (Subgroup.mem_comap.1 hf'.2) (π t') (Subgroup.mem_comap.1 ht')
  have hFnorm : (WE ⊓ FM.comap π).map K.subtype ≤
      Subgroup.normalizer (((TM.comap π).map K.subtype : Subgroup G) : Set G) := by
    intro f hf
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hconj f hf h hh
    · intro hh
      have h2 := hconj f⁻¹ (Subgroup.inv_mem _ hf) _ hh
      convert h2 using 1
      group
  have hcomm_ne : (⁅(TM.comap π).map K.subtype, (WE ⊓ FM.comap π).map K.subtype⁆ : Subgroup G) ≠ ⊥ := by
    obtain ⟨t, ht, f, hf, htf⟩ := hTc
    obtain ⟨x, hxπ⟩ := hπs t
    have hx : x ∈ TM.comap π := by
      rw [Subgroup.mem_comap, hxπ]
      exact ht
    have hfE : f ∈ WE.map π := hWEmap ▸ hFE hf
    obtain ⟨y, hyWE, hyf⟩ := Subgroup.mem_map.1 hfE
    have hy : y ∈ WE ⊓ FM.comap π :=
      Subgroup.mem_inf.2 ⟨hyWE, Subgroup.mem_comap.2 (by rw [hyf]; exact hf)⟩
    intro hbot
    have hmem := Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem K.subtype hx)
      (Subgroup.mem_map_of_mem K.subtype hy)
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hmem
    have h2 : x * y = y * x := Subtype.ext hmem
    have h3 := congrArg π h2
    rw [map_mul, map_mul, hxπ, hyf] at h3
    apply htf
    exact h3
  have hN3 : ¬ 3 ∣ Nat.card (GLAPPrimeCore 3 ↥K) := by
    have h := not_dvd_card_glaPPrimeCoreOf Nat.prime_three K
    unfold GLAPPrimeCoreOf at h
    rwa [Subgroup.card_map_of_injective K.subtype_injective] at h
  have hsimpleM : IsSimpleGroup M := by
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hK.2
    exact e.symm.isSimpleGroup
  have hnotN : ¬ (TM.comap π).map K.subtype ≤ GLAPPrimeCoreOf 3 K := by
    intro hle
    have hN : ∀ x ∈ TM.comap π, x ∈ GLAPPrimeCore 3 ↥K := by
      intro x hx
      have hmem : (x : G) ∈ GLAPPrimeCoreOf 3 K := hle (Subgroup.mem_map_of_mem K.subtype hx)
      unfold GLAPPrimeCoreOf at hmem
      obtain ⟨n, hn, hnx⟩ := Subgroup.mem_map.1 hmem
      have hnx' : n = x := Subtype.ext hnx
      rwa [hnx'] at hn
    have hNm : ((GLAPPrimeCore 3 ↥K).map π).Normal := Subgroup.Normal.map inferInstance π hπs
    rcases hsimpleM.eq_bot_or_eq_top_of_normal ((GLAPPrimeCore 3 ↥K).map π) with h | h
    · obtain ⟨t, ht, f, hf, htf⟩ := hTc
      obtain ⟨x, hxπ⟩ := hπs t
      have hx : x ∈ TM.comap π := by
        rw [Subgroup.mem_comap, hxπ]
        exact ht
      have hmem : π x ∈ (GLAPPrimeCore 3 ↥K).map π := Subgroup.mem_map_of_mem π (hN x hx)
      rw [h, Subgroup.mem_bot] at hmem
      have ht1 : t = 1 := by
        rw [← hxπ]
        exact hmem
      apply htf
      rw [ht1, one_mul, mul_one]
    · have hg1 : gM ≠ 1 := fun h1 => hgF (h1 ▸ one_mem FM)
      have hg3' : gM ^ 3 = 1 := hEel.2 gM hgE
      haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hord : orderOf gM = 3 := orderOf_eq_prime hg3' hg1
      have hgmem : gM ∈ (GLAPPrimeCore 3 ↥K).map π := by
        rw [h]
        exact Subgroup.mem_top _
      obtain ⟨n, hn, hnπ⟩ := Subgroup.mem_map.1 hgmem
      have hdvd : orderOf gM ∣ orderOf n := by
        rw [← hnπ]
        exact orderOf_map_dvd π n
      have hdvd2 : orderOf n ∣ Nat.card (GLAPPrimeCore 3 ↥K) := Subgroup.orderOf_dvd_natCard _ hn
      have h3 : 3 ∣ orderOf gM := by rw [hord]
      exact hN3 ((h3.trans hdvd).trans hdvd2)
  obtain ⟨w, hwWE, hwg⟩ : ∃ w ∈ WE, π w = gM := by
    have hgWE : gM ∈ WE.map π := hWEmap ▸ hgE
    obtain ⟨w, hw, hwg⟩ := Subgroup.mem_map.1 hgWE
    exact ⟨w, hw, hwg⟩
  have hgex : ∃ g ∈ K ⊓ Subgroup.centralizer (((WE ⊓ FM.comap π).map K.subtype : Subgroup G) : Set G),
      g ^ 3 = 1 ∧ g ∉ (WE ⊓ FM.comap π).map K.subtype := by
    refine ⟨(w : G), Subgroup.mem_inf.2 ⟨w.2, ?_⟩, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro f hf
      obtain ⟨f', hf', rfl⟩ := Subgroup.mem_map.1 hf
      have hc : f' * w = w * f' := congrArg Subtype.val (hWEcomm ⟨f', hF'WE hf'⟩ ⟨w, hwWE⟩)
      have hc' : (f' : G) * (w : G) = (w : G) * (f' : G) := congrArg Subtype.val hc
      exact hc'
    · have h4 : (w : ↥K) ^ 3 = 1 := by simpa using congrArg Subtype.val (hWEexp ⟨w, hwWE⟩)
      have h5 := congrArg Subtype.val h4
      simpa using h5
    · intro hmem
      obtain ⟨f', hf', hfe⟩ := Subgroup.mem_map.1 hmem
      have hf'w : f' = w := Subtype.ext hfe
      rw [hf'w] at hf'
      exact hgF (hwg ▸ Subgroup.mem_comap.1 hf'.2)
  have hcentK : ∀ g ∈ K ⊓ Subgroup.centralizer (K : Set G), g ^ 3 = 1 → g = 1 := by
    intro g hg h3
    obtain ⟨hgK, hgc⟩ := Subgroup.mem_inf.1 hg
    have hgZ : (⟨g, hgK⟩ : ↥K) ∈ Z := by
      rw [hZdef, Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hgc y.1 y.2)
    have hg3 : (⟨g, hgK⟩ : ↥K) ^ 3 = 1 := Subtype.ext h3
    exact congrArg Subtype.val (hZtriv _ hgZ hg3)
  exact ⟨(WE ⊓ FM.comap π).map K.subtype, (TM.comap π).map K.subtype, WE.map K.subtype, hFK,
    hFel, hFcard, hTK, hTp, hFnorm, hcomm_ne, hempty, hnotN, hgex, hEK, hWEel,
    by rw [hWEcard, hEc], hcentK⟩

@[expose] def plOf {n : ℕ} : Fin n ⊕ Fin n → Fin n
  | .inl i => i
  | .inr i => i

@[expose] def ixOf {n : ℕ} : Fin n ⊕ Fin n → Fin 2
  | .inl _ => 0
  | .inr _ => 1

@[expose] def pb {n : ℕ} {R : Type} [Zero R] (P : Fin n → Matrix (Fin 2) (Fin 2) R) :
    Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) R :=
  Matrix.of fun x y => if plOf x = plOf y then P (plOf x) (ixOf x) (ixOf y) else 0

theorem pb_apply {n : ℕ} {R : Type} [Zero R] (P : Fin n → Matrix (Fin 2) (Fin 2) R)
    (x y : Fin n ⊕ Fin n) :
    pb P x y = if plOf x = plOf y then P (plOf x) (ixOf x) (ixOf y) else 0 := rfl

theorem sum_plane {n : ℕ} {R : Type} [AddCommMonoid R] (k : Fin n) (g : Fin 2 → R) :
    ∑ z : Fin n ⊕ Fin n, (if k = plOf z then g (ixOf z) else 0) = g 0 + g 1 := by
  rw [Fintype.sum_sum_type]
  change (∑ a : Fin n, if k = a then g 0 else 0) + (∑ a : Fin n, if k = a then g 1 else 0) =
    g 0 + g 1
  simp

theorem pb_mul {n : ℕ} {R : Type} [CommRing R] (P Q : Fin n → Matrix (Fin 2) (Fin 2) R) :
    pb P * pb Q = pb (fun i => P i * Q i) := by
  ext x y
  rw [Matrix.mul_apply]
  by_cases hxy : plOf x = plOf y
  · have key : ∀ z : Fin n ⊕ Fin n, pb P x z * pb Q z y =
        if plOf x = plOf z then P (plOf x) (ixOf x) (ixOf z) * Q (plOf x) (ixOf z) (ixOf y)
        else 0 := by
      intro z
      rw [pb_apply, pb_apply, ← hxy]
      by_cases h : plOf x = plOf z
      · simp [h, eq_comm]
      · simp [h, eq_comm]
    simp only [key]
    rw [sum_plane (plOf x) (fun s => P (plOf x) (ixOf x) s * Q (plOf x) s (ixOf y)),
      pb_apply, if_pos hxy]
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  · have key : ∀ z : Fin n ⊕ Fin n, pb P x z * pb Q z y = 0 := by
      intro z
      rw [pb_apply, pb_apply]
      by_cases h1 : plOf x = plOf z <;> by_cases h2 : plOf z = plOf y <;> simp_all
    simp only [key, Finset.sum_const_zero]
    rw [pb_apply, if_neg hxy]

theorem pb_one {n : ℕ} {R : Type} [CommRing R] :
    pb (fun _ : Fin n => (1 : Matrix (Fin 2) (Fin 2) R)) = 1 := by
  ext x y
  rw [pb_apply, Matrix.one_apply]
  rcases x with i | i <;> rcases y with j | j <;> simp [plOf, ixOf, Matrix.one_apply, Fin.ext_iff]

@[expose] def mkSpG {n : ℕ} {K : Type} [Field K] (M N : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) K)
    (h1 : M * N = 1) (h2 : N * M = 1)
    (hs : (Matrix.transpose M) * Matrix.fromBlocks 0 1 (-1) 0 * M =
      (Matrix.fromBlocks 0 1 (-1) 0 : Matrix _ _ K)) :
    StatedSp n K :=
  ⟨⟨M, N, h1, h2⟩, CFSG.Open.StatedAPI.mem_statedSp_iff.2 hs⟩

@[expose] def emb13 : Multiplicative (ZMod 3 × ZMod 3) →* Multiplicative (ZMod 3 × ZMod 3 × ZMod 3)
    where
  toFun v := Multiplicative.ofAdd (v.toAdd.1, 0, v.toAdd.2)
  map_one' := rfl
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    simp [toAdd_mul]

theorem emb13_injective : Function.Injective emb13 := by
  intro x y h
  apply Multiplicative.toAdd.injective
  have h' := congrArg Multiplicative.toAdd h
  simp only [emb13, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, Prod.mk.injEq] at h'
  exact Prod.ext h'.1 h'.2.2

theorem stdSub_of_tau {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : CFSG.Open.IsQuasisimple ↥K) {M : Type} [Group M] [Finite M]
    (e : ↥K ⧸ Subgroup.center ↥K ≃* M) (hZ : Nat.card (Subgroup.center ↥K) ∣ 2)
    (τ : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3) →* M) (hτ : Function.Injective τ)
    {TM : Subgroup M} (hT2 : IsPGroup 2 TM) (hT8 : 8 < Nat.card TM)
    (hFN : ∀ x : Multiplicative (ZMod 3 × ZMod 3), ∀ t ∈ TM,
      τ (emb13 x) * t * (τ (emb13 x))⁻¹ ∈ TM)
    (hTc : ∃ t ∈ TM, ∃ x : Multiplicative (ZMod 3 × ZMod 3),
      t * τ (emb13 x) ≠ τ (emb13 x) * t) :
    ∃ F T E : Subgroup G, F ≤ K ∧ IsElemAbelian 3 F ∧ Nat.card F = 3 ^ 2 ∧ T ≤ K ∧
      IsPGroup 2 T ∧ F ≤ Subgroup.normalizer (T : Set G) ∧ (⁅T, F⁆ : Subgroup G) ≠ ⊥ ∧
      IsEmpty (T ≃* QuaternionGroup 2) ∧ ¬ T ≤ GLAPPrimeCoreOf 3 K ∧
      (∃ g ∈ K ⊓ Subgroup.centralizer (F : Set G), g ^ 3 = 1 ∧ g ∉ F) ∧
      E ≤ K ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 3 ∧
      (∀ g ∈ K ⊓ Subgroup.centralizer (K : Set G), g ^ 3 = 1 → g = 1) := by
  classical
  have hpow : ∀ a : Multiplicative (ZMod 3 × ZMod 3 × ZMod 3), a ^ 3 = 1 := by
    intro a; revert a; decide
  have hEc : Nat.card τ.range = 3 ^ 3 := by
    rw [card_range_eq_of_injective τ hτ, Nat.card_congr Multiplicative.toAdd, Nat.card_prod,
      Nat.card_prod, Nat.card_zmod]
    norm_num
  have hFc : Nat.card (τ.comp emb13).range = 3 ^ 2 := by
    rw [card_range_eq_of_injective (τ.comp emb13) (hτ.comp emb13_injective),
      Nat.card_congr Multiplicative.toAdd,
      Nat.card_prod, Nat.card_zmod]
    norm_num
  have hgF : τ (Multiplicative.ofAdd ((0 : ZMod 3), (1 : ZMod 3), (0 : ZMod 3))) ∉
      (τ.comp emb13).range := by
    intro h
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 h
    have h2 := hτ hx
    have h3 := congrArg (fun z => Multiplicative.toAdd z |>.2.1) h2
    simp [emb13] at h3
  have hZpos : 0 < Nat.card (Subgroup.center ↥K) := Nat.pos_of_dvd_of_pos hZ (by norm_num)
  have hTcard : Nat.card (Subgroup.center ↥K) * Nat.card TM ≠ 8 := by
    intro h
    have : 1 * Nat.card TM ≤ Nat.card (Subgroup.center ↥K) * Nat.card TM :=
      Nat.mul_le_mul_right _ hZpos
    omega
  obtain ⟨F, T, E, h⟩ := stdSub_of_model hK e hZ (EM := τ.range) (FM := (τ.comp emb13).range)
    (TM := TM) (gM := τ (Multiplicative.ofAdd ((0 : ZMod 3), (1 : ZMod 3), (0 : ZMod 3))))
    (isElemAbelian_range τ hpow) hEc
    (fun f hf => by
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hf
      exact MonoidHom.mem_range.2 ⟨_, rfl⟩) hFc (MonoidHom.mem_range.2 ⟨_, rfl⟩) hgF hT2
    (fun f hf t ht => by
      obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hf
      exact hFN x t ht)
    (by
      obtain ⟨t, ht, x, hx⟩ := hTc
      exact ⟨t, ht, _, ⟨x, rfl⟩, hx⟩)
    hTcard
  exact ⟨F, T, E, h⟩

end CFSG.LocalAnalysis.GLTheoremA.CatB
