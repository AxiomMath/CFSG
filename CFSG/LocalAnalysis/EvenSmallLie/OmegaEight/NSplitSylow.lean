module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitMain
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitDict

public section

namespace CFSG.EvenSmallLie.OmegaEight.NSplit

open Subgroup CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.EvenSmallLie.OmegaEight.SpBranch

attribute [local irreducible] sAct sMt sGinv p9List p9Index

variable {G : Type*} [Group G]

namespace Branch

variable {ε : Eps} {t : G} {Q TH : Subgroup G} {ψ : V6 → G} (hB : Branch ε t Q TH ψ)
include hB


@[expose] noncomputable def sec : affGroup ε →* normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  hB.exists_section.choose

theorem piHom_sec (g : affGroup ε) : hB.piHom (hB.sec g) = g := hB.exists_section.choose_spec g

theorem ι_zero : hB.ι 0 = 1 := by
  have h := hB.ι_add 0 0
  rw [add_zero] at h
  exact mul_eq_left.1 h.symm

omit [Group G] hB
  in
theorem kV_zero : kV ε 0 = 0 := by
  have h := kV_xor ε (by norm_num : 0 < 128) (by norm_num : 0 < 128)
  rw [Nat.xor_self] at h
  have h2 : kV ε 0 + kV ε 0 = kV ε 0 + 0 := by rw [add_zero, ← h]
  exact add_left_cancel h2

theorem sec_conj (g : affGroup ε) (y : V7) :
    hB.sec g * hB.ι y = hB.ι (rhoE ε g y) * hB.sec g := by
  have h := hB.conj_ι (hB.sec g) y
  rw [hB.piHom_sec] at h
  rw [← h]
  group

omit hB in
@[expose] noncomputable def phiN (ε : Eps) (i : ℕ) : affGroup ε :=
  if h : i < 512 then phiG ε ⟨i, h⟩ else 1

omit hB in
theorem phiN_sM {i j : ℕ} (hi : i < 512) (hj : j < 512) :
    phiN ε (sM i j) = phiN ε i * phiN ε j := by
  rw [phiN, dite_eq_left (sM_lt hi hj), phiN, dite_eq_left hi, phiN, dite_eq_left hj]
  exact phiG_sM ε ⟨i, hi⟩ ⟨j, hj⟩

omit hB in
theorem kV_sA' {i e : ℕ} (hi : i < 512) (he : e < 128) :
    kV ε (sA i e) = rhoE ε (phiN ε i) (kV ε e) := by
  rw [phiN, dite_eq_left hi]
  exact kV_sA ε ⟨i, hi⟩ he

@[expose] noncomputable def jFun (x : SModel) : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) :=
  hB.ι (kV ε (eP x.code)) * hB.sec (phiN ε (gP x.code))

theorem jFun_mul (x y : SModel) : hB.jFun (x * y) = hB.jFun x * hB.jFun y := by
  simp only [jFun, SModel.code_mul, eP_sMul, gP_sMul]
  rw [phiN_sM (gP_lt _) (gP_lt _), kV_xor ε (eP_lt _) (sA_lt (gP_lt _) (eP_lt _)),
    kV_sA' (gP_lt _) (eP_lt _), hB.ι_add, map_mul]
  have h := hB.sec_conj (phiN ε (gP x.code)) (kV ε (eP y.code))
  calc hB.ι (kV ε (eP x.code)) * hB.ι (rhoE ε (phiN ε (gP x.code)) (kV ε (eP y.code))) *
        (hB.sec (phiN ε (gP x.code)) * hB.sec (phiN ε (gP y.code)))
      = hB.ι (kV ε (eP x.code)) * (hB.ι (rhoE ε (phiN ε (gP x.code)) (kV ε (eP y.code))) *
        hB.sec (phiN ε (gP x.code))) * hB.sec (phiN ε (gP y.code)) := by group
    _ = hB.ι (kV ε (eP x.code)) * (hB.sec (phiN ε (gP x.code)) * hB.ι (kV ε (eP y.code))) *
        hB.sec (phiN ε (gP y.code)) := by rw [h]
    _ = _ := by group

@[expose] noncomputable def jHom : SModel →* normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G) where
  toFun := hB.jFun
  map_one' := by
    simp only [jFun, SModel.code_one, show eP 0 = 0 from rfl, show gP 0 = 0 from rfl]
    rw [kV_zero, hB.ι_zero, phiN, dite_eq_left (by norm_num), phiG_zero, map_one, mul_one]
  map_mul' := hB.jFun_mul

theorem piHom_jHom (x : SModel) : hB.piHom (hB.jHom x) = phiN ε (gP x.code) := by
  change hB.piHom (hB.ι _ * hB.sec _) = _
  rw [map_mul, hB.piHom_ι, hB.piHom_sec, one_mul]

omit hB in
theorem phiN_eq_one {i : ℕ} (hi : i < 512) (h : phiN ε i = 1) : i = 0 := by
  rw [phiN, dite_eq_left hi] at h
  exact phiG_eq_one ε h

theorem jHom_injective : Function.Injective hB.jHom := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  rw [MonoidHom.mem_ker] at hx
  have hg : gP x.code = 0 := by
    have h1 := hB.piHom_jHom x
    rw [hx, map_one] at h1
    exact phiN_eq_one (gP_lt _) h1.symm
  have h2 : hB.ι (kV ε (eP x.code)) = 1 := by
    have h3 : hB.jHom x = hB.ι (kV ε (eP x.code)) * hB.sec (phiN ε (gP x.code)) := rfl
    rw [hx, hg, phiN, dite_eq_left (by norm_num), phiG_zero, map_one, mul_one] at h3
    exact h3.symm
  have he : eP x.code = 0 := by
    rw [← hB.ι_zero, ← kV_zero] at h2
    exact kV_injective ε (eP_lt _) (by norm_num) (hB.ι_inj h2)
  rw [mem_bot]
  apply SModel.ext
  rw [SModel.code_one, eq_of_parts x.lt, he, hg]

theorem jHom_mem_E_iff (x : SModel) :
    ((hB.jHom x : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) : G) ∈ Q ⊔ zpowers t ↔
      x ∈ SModel.EM := by
  rw [← hB.piHom_eq_one_iff, hB.piHom_jHom]
  change _ ↔ x.code < 128
  constructor
  · intro h
    have hg := phiN_eq_one (gP_lt _) h
    rw [eq_of_parts x.lt, hg]
    have := eP_lt x.code
    omega
  · intro h
    have hg : gP x.code = 0 := by
      unfold gP
      rw [Nat.div_eq_of_lt h]
    rw [hg, phiN, dite_eq_left (by norm_num), phiG_zero]

end Branch

theorem card_of_maximal {A : Type*} [Group A] [Finite A] {p : ℕ} [Fact p.Prime] {H K : Subgroup A}
    (hHK : H ≤ K) (hH : IsPGroup p H)
    (hmax : ∀ V : Subgroup A, V ≤ K → IsPGroup p V → H ≤ V → V = H) :
    Nat.card H = p ^ (Nat.card K).factorization p := by
  have hH' : IsPGroup p (H.subgroupOf K) :=
    hH.of_equiv (Subgroup.subgroupOfEquivOfLe hHK).symm
  obtain ⟨P, hP⟩ := hH'.exists_le_sylow
  have hV : (P : Subgroup K).map K.subtype = H := by
    apply hmax
    · rintro _ ⟨y, -, rfl⟩; exact y.2
    · exact P.isPGroup'.map K.subtype
    · intro x hx
      exact ⟨⟨x, hHK hx⟩, hP hx, rfl⟩
  rw [← hV, Subgroup.card_map_of_injective K.subtype_injective, Sylow.card_eq_multiplicity]

theorem factorization_two_mul (k m : ℕ) (hm : Odd m) : (2 ^ k * m).factorization 2 = k := by
  have hm0 : m ≠ 0 := (Odd.pos hm).ne'
  rw [Nat.factorization_mul (by positivity) hm0, Finsupp.add_apply,
    Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd
      (fun h => (Nat.not_even_iff_odd.2 hm) (even_iff_two_dvd.2 h)),
    add_zero]

theorem card_V7 : Nat.card V7 = 128 := by
  rw [Nat.card_eq_fintype_card]
  simp [ZMod.card]

namespace Branch

variable {ε : Eps} {t : G} {Q TH : Subgroup G} {ψ : V6 → G} (hB : Branch ε t Q TH ψ)
include hB


theorem card_ker : Nat.card hB.piHom.ker = 128 := by
  rw [← card_V7]
  symm
  refine Nat.card_congr (Equiv.ofBijective (fun x => ⟨hB.ι x, hB.piHom_ι x⟩) ⟨?_, ?_⟩)
  · intro x y h
    exact hB.ι_inj (congrArg Subtype.val h)
  · rintro ⟨n, hn⟩
    obtain ⟨x, hx⟩ := hB.exists_ι_of_piHom n hn
    exact ⟨x, Subtype.ext hx⟩

theorem card_N [Finite G] :
    Nat.card (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) = 128 * 1451520 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup hB.piHom.ker, hB.card_ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hB.piHom_surjective).toEquiv,
    card_affGroup, mul_comm]

@[expose] def stab0 (ε : Eps) : Subgroup (affGroup ε) where
  carrier := {σ | alphaZ ε σ (ω0 ε) = ω0 ε}
  mul_mem' {a b} ha hb := by
    simp only [Set.mem_ofPred_eq, map_mul, Equiv.Perm.coe_mul, Function.comp_apply] at *
    rw [hb, ha]
  one_mem' := by simp
  inv_mem' {a} ha := by
    simp only [Set.mem_ofPred_eq, map_inv] at *
    conv_lhs => rw [← ha]
    exact perm_inv_apply' _ _

omit hB in
theorem card_stab0_le : Nat.card (stab0 ε) ≤ oBound ε := by
  have hinj : Function.Injective fun σ : stab0 ε =>
      (⟨((σ : affGroup ε) : Equiv.Perm V6), mem_orthGroup_of_mem_affGroup (σ : affGroup ε).2
        ((alphaZ_ω0_iff σ.1).1 σ.2)⟩ : orthGroup ε) := by
    intro σ τ h
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  exact (Nat.card_le_card_of_injective _ hinj).trans (card_orthGroup_le ε)

omit hB in
theorem card_stab0 : Nat.card (stab0 ε) = oBound ε := by
  have h1 := card_stab0_le (ε := ε)
  have hidx : (stab0 ε).index ≤ mOf ε := by
    let _ : MulAction (affGroup ε) (Fin (mOf ε)) := MulAction.compHom _ (alphaZ ε)
    have hst : MulAction.stabilizer (affGroup ε) (ω0 ε) = stab0 ε := by
      ext σ
      rfl
    rw [← hst, MulAction.index_stabilizer]
    calc (MulAction.orbit (affGroup ε) (ω0 ε)).ncard ≤ (Set.univ : Set (Fin (mOf ε))).ncard :=
          Set.ncard_le_ncard (Set.subset_univ _)
      _ = mOf ε := by rw [Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  have h2 := Subgroup.card_mul_index (stab0 ε)
  rw [card_affGroup] at h2
  have h3 : mOf ε * oBound ε = 1451520 := by cases ε <;> rfl
  have h4 : 0 < (stab0 ε).index := Nat.pos_of_ne_zero (by
    intro h; rw [h, mul_zero] at h2; exact absurd h2 (by norm_num))
  nlinarith

theorem stabN_eq : hB.stabN = (stab0 ε).comap hB.piHom := rfl

theorem card_stabN [Finite G] : Nat.card hB.stabN = 128 * oBound ε := by
  have h1 := Subgroup.card_mul_index hB.stabN
  rw [hB.stabN_eq, Subgroup.index_comap_of_surjective _ hB.piHom_surjective, hB.card_N] at h1
  have h2 := Subgroup.card_mul_index (stab0 ε)
  rw [card_stab0, card_affGroup] at h2
  have h3 : mOf ε * oBound ε = 1451520 := by cases ε <;> rfl
  have hob : 0 < oBound ε := by cases ε <;> decide
  have hidx : (stab0 ε).index = mOf ε := by
    have : oBound ε * (stab0 ε).index = oBound ε * mOf ε := by rw [h2, mul_comm, h3]
    exact Nat.eq_of_mul_eq_mul_left hob this
  rw [hidx] at h1
  have hm : 0 < mOf ε := by cases ε <;> decide
  have : Nat.card ((stab0 ε).comap hB.piHom) * mOf ε = (128 * oBound ε) * mOf ε := by
    rw [h1, mul_assoc, mul_comm (oBound ε), h3]
  exact Nat.eq_of_mul_eq_mul_right hm this

theorem mem_stabN_iff (n : normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :
    n ∈ hB.stabN ↔ (n : G) * t = t * n := by
  change alphaZ ε (hB.piHom n) (ω0 ε) = ω0 ε ↔ _
  rw [hB.stab_iff]
  constructor
  · intro h
    calc (n : G) * t = (n * t * (n : G)⁻¹) * n := by group
      _ = t * n := by rw [h]
  · intro h; rw [h, mul_inv_cancel_right]

omit hB in
@[expose] def thN (t : G) (Q TH : Subgroup G) :
    Subgroup (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)) :=
  TH.subgroupOf (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G))

theorem thN_pgroup : IsPGroup 2 (thN t Q TH) :=
  hB.TH_pgroup.of_equiv (Subgroup.subgroupOfEquivOfLe hB.TH_le_normalizer).symm

theorem thN_le_stabN : thN t Q TH ≤ hB.stabN := fun x hx =>
  (hB.mem_stabN_iff x).2 (mem_centralizer_singleton_iff.1 (hB.TH_le hx))

theorem card_TH [Finite G] : Nat.card TH = 2 ^ 14 := by
  have hc := card_of_maximal (p := 2) hB.thN_le_stabN hB.thN_pgroup (fun V hV hp hle => by
    have hV' : V.map (normalizer ((Q ⊔ zpowers t : Subgroup G) : Set G)).subtype = TH := by
      apply hB.TH_max
      · rintro _ ⟨y, hy, rfl⟩
        exact mem_centralizer_singleton_iff.2 ((hB.mem_stabN_iff y).1 (hV hy))
      · exact hp.map _
      · intro x hx
        exact ⟨⟨x, hB.TH_le_normalizer hx⟩, hle hx, rfl⟩
    apply le_antisymm
    · intro x hx
      have : (x : G) ∈ TH := hV' ▸ ⟨x, hx, rfl⟩
      exact this
    · exact hle)
  rw [hB.card_stabN] at hc
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB.TH_le_normalizer).toEquiv]
  change Nat.card (thN t Q TH) = _
  rw [hc]
  cases ε
  · rw [show 128 * oBound .plus = 2 ^ 14 * 315 by rfl, factorization_two_mul 14 315 (by decide)]
  · rw [show 128 * oBound .minus = 2 ^ 14 * 405 by rfl, factorization_two_mul 14 405 (by decide)]

end Branch

theorem card_centralizer_map {A B : Type*} [Group A] [Group B] (f : A ≃* B) (a : A) :
    Nat.card (centralizer ({f a} : Set B)) = Nat.card (centralizer ({a} : Set A)) := by
  have h : centralizer ({f a} : Set B) = (centralizer ({a} : Set A)).map f.toMonoidHom := by
    ext x
    simp only [mem_centralizer_singleton_iff, Subgroup.mem_map, MulEquiv.coe_toMonoidHom]
    constructor
    · intro hx
      refine ⟨f.symm x, ?_, by simp⟩
      apply f.injective
      simp [map_mul, hx]
    · rintro ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hy]
  rw [h, Subgroup.card_map_of_injective f.injective]

theorem card_conj_orbit {A : Type*} [Group A] [Finite A] (a : A) :
    Nat.card (MulAction.orbit (ConjAct A) a) * Nat.card (centralizer ({a} : Set A)) =
      Nat.card A := by
  have e := MulAction.orbitProdStabilizerEquivGroup (ConjAct A) a
  rw [← Nat.card_congr (ConjAct.ofConjAct (G := A)).toEquiv, ← Nat.card_congr e, Nat.card_prod,
    ConjAct.stabilizer_eq_centralizer, card_centralizer_map (ConjAct.toConjAct (G := A)) a]

section SModelConj


theorem gP_of_lt {c : ℕ} (hc : c < 128) : gP c = 0 := by
  unfold gP
  rw [Nat.div_eq_of_lt hc]

theorem eP_of_lt {c : ℕ} (hc : c < 128) : eP c = c := Nat.mod_eq_of_lt hc

theorem sM_inv_right (y : SModel) : sM (gP y.code) (sGinv[gP y.code]!) = 0 := by
  have h : (y * y⁻¹).code = 0 := by rw [mul_inv_cancel]; rfl
  rw [SModel.code_mul, SModel.code_inv] at h
  have := congrArg gP h
  rwa [gP_sMul, gP_sInv, show gP 0 = 0 from rfl] at this

theorem conj_code (y c : SModel) (hc : c.code < 128) :
    (y * c * y⁻¹).code = sA (gP y.code) c.code := by
  have hlt : sA (gP y.code) c.code < 128 := sA_lt (gP_lt _) hc
  rw [SModel.code_mul, SModel.code_mul, SModel.code_inv]
  apply ext_parts (sMul_lt _ _) (by omega)
  · rw [eP_sMul, eP_sMul, eP_sInv, gP_sMul, gP_of_lt hc, (sM_unit (gP_lt _)).2.1, eP_of_lt hc,
      eP_of_lt hlt]
    rw [← sA_mul (gP_lt _) (sGinv_lt (gP_lt _)) (eP_lt _), sM_inv_right, sA_zero (eP_lt _),
      Nat.xor_comm (eP y.code), Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  · rw [gP_sMul, gP_sMul, gP_sInv, gP_of_lt hc, (sM_unit (gP_lt _)).2.1, sM_inv_right,
      gP_of_lt hlt]

@[expose] def pElt (g : ℕ) (hg : g < 512) : SModel := ⟨128 * g, by omega⟩

theorem gP_pElt {g : ℕ} (hg : g < 512) : gP (pElt g hg).code = g := by
  simp only [pElt, gP]
  rw [Nat.mul_div_cancel_left _ (by norm_num), Nat.mod_eq_of_lt hg]

theorem card_orbit_eq (c : SModel) (hc : c.code < 128) :
    Nat.card (MulAction.orbit (ConjAct SModel) c) = (p9Orbit c.code).length := by
  have hnd : (p9Orbit c.code).Nodup := List.nodup_dedup _
  rw [← List.toFinset_card_of_nodup hnd, ← Nat.card_eq_finsetCard]
  refine Nat.card_congr (Equiv.ofBijective (fun z => ⟨z.1.code, ?_⟩) ⟨?_, ?_⟩)
  · obtain ⟨y, hy⟩ := z.2
    rw [← hy]
    change (y • c).code ∈ _
    rw [ConjAct.smul_def, conj_code _ _ hc]
    simp only [List.mem_toFinset, p9Orbit, List.mem_dedup, List.mem_map, List.mem_range]
    exact ⟨_, gP_lt _, rfl⟩
  · intro z z' h
    exact Subtype.ext (SModel.ext (congrArg Subtype.val h))
  · rintro ⟨e, he⟩
    simp only [List.mem_toFinset, p9Orbit, List.mem_dedup, List.mem_map, List.mem_range] at he
    obtain ⟨g, hg, rfl⟩ := he
    refine ⟨⟨pElt g hg * c * (pElt g hg)⁻¹, ConjAct.toConjAct (pElt g hg), ?_⟩, ?_⟩
    · change ConjAct.toConjAct (pElt g hg) • c = _
      rw [ConjAct.smul_def]; simp
    · apply Subtype.ext
      simp only
      rw [conj_code _ _ hc, gP_pElt]

end SModelConj

end CFSG.EvenSmallLie.OmegaEight.NSplit
