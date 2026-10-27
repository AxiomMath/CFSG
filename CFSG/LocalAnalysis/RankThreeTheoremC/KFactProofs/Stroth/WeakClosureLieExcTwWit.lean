module

public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwMove
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.HardMathSupport.Timmesfeld.LangTorus
open scoped commutatorElement Matrix

section Vec

variable {τ : Tag} {L : Type} [Field L]

theorem prod_zpow_eq_zpow_sum' {G : Type*} [CommGroup G] (g : G) {ι : Type*} (s : Finset ι)
    (c : ι → ℤ) : ∏ i ∈ s, g ^ c i = g ^ ∑ i ∈ s, c i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, zpow_add, ih]

theorem rootChar_zpow_vec (ζ : Lˣ) (b x : Fin τ.rank → ℤ) :
    rootChar (fun i => ζ ^ b i) x = ζ ^ ∑ i, b i * x i := by
  unfold rootChar
  simp_rw [← zpow_mul]
  exact prod_zpow_eq_zpow_sum' ζ Finset.univ _

theorem tw_mem_fixedCharTuples_of_vec {ζ : Lˣ} {p : ℕ} (hζ : ζ ^ p = 1) {b : Fin τ.rank → ℤ}
    {M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    (h : ∀ j, (p : ℤ) ∣ (M.transpose *ᵥ b) j - q * b j) :
    (fun i => ζ ^ b i) ∈ fixedCharTuples M Fr := by
  rw [mem_fixedCharTuples_iff]
  intro x
  rw [CTTorus.map_units_eq_pow hFr, rootChar_zpow_vec, rootChar_zpow_vec, ← zpow_natCast,
    ← zpow_mul]
  have hdiv : (p : ℤ) ∣ (∑ i, b i * (M *ᵥ x) i) - (∑ i, b i * x i) * q := by
    have e1 : (∑ i, b i * (M *ᵥ x) i) = ∑ i, (M.transpose *ᵥ b) i * x i := by
      have := Matrix.dotProduct_mulVec b M x
      rw [Matrix.mulVec_transpose]
      exact this
    have e2 : (∑ i, b i * x i) * q = ∑ i, (q * b i) * x i := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e1, e2, ← Finset.sum_sub_distrib]
    exact Finset.dvd_sum fun i _ => by rw [← sub_mul]; exact Dvd.dvd.mul_right (h i) _
  obtain ⟨c, hc⟩ := hdiv
  have e : (∑ i, b i * (M *ᵥ x) i) = (∑ i, b i * x i) * q + p * c := by linarith
  rw [e, zpow_add, zpow_mul ζ (p : ℤ) c, zpow_natCast, hζ, one_zpow, mul_one]

theorem weylTuple_zpow_vec {ζ : Lˣ} {b : Fin τ.rank → ℤ} {u : WeylGroup τ}
    {N : Matrix (Fin τ.rank) (Fin τ.rank) ℤ} (hN : ∀ x, u⁻¹ • x = N *ᵥ x) (i : Fin τ.rank) :
    weylTuple u (fun i => ζ ^ b i) i = ζ ^ ((N.transpose *ᵥ b) i) := by
  have e0 : weylTuple u (fun i => ζ ^ b i) i =
      rootChar (fun i => ζ ^ b i) (u⁻¹ • (Pi.single i 1 : Fin τ.rank → ℤ)) := rfl
  rw [e0, hN, rootChar_zpow_vec]
  congr 1
  simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.transpose_apply]
  exact Finset.sum_congr rfl fun i _ => mul_comm _ _

theorem tw_weylTuple_ne_of_vec {ζ : Lˣ} {p : ℕ} (hζ : orderOf ζ = p) {b : Fin τ.rank → ℤ}
    {u : WeylGroup τ} {N : Matrix (Fin τ.rank) (Fin τ.rank) ℤ}
    (hN : ∀ x, u⁻¹ • x = N *ᵥ x) {i₀ : Fin τ.rank}
    (h : ¬ (p : ℤ) ∣ (N.transpose *ᵥ b) i₀ - b i₀) :
    weylTuple u (fun i => ζ ^ b i) ≠ fun i => ζ ^ b i := by
  intro heq
  have h1 := congrFun heq i₀
  have h2 : weylTuple u (fun i => ζ ^ b i) i₀ = ζ ^ ((N.transpose *ᵥ b) i₀) := by
    have e0 : weylTuple u (fun i => ζ ^ b i) i₀ =
        rootChar (fun i => ζ ^ b i) (u⁻¹ • (Pi.single i₀ 1 : Fin τ.rank → ℤ)) := rfl
    rw [e0, hN, rootChar_zpow_vec]
    congr 1
    simp only [Matrix.mulVec, dotProduct, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, Matrix.transpose_apply]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [h2] at h1
  have h3 : ζ ^ ((N.transpose *ᵥ b) i₀ - b i₀) = 1 := by
    rw [zpow_sub, h1, mul_inv_cancel]
  apply h
  have := (orderOf_dvd_iff_zpow_eq_one (G := Lˣ)).2 h3
  rwa [hζ] at this

end Vec

section Witness

variable {t : TwistTag} {L : Type} [Field L] [IsAlgClosed L]
  (D : LangDatum t.tag L)

theorem TwActsAs.pow {y : ModGL t.tag L} {u : WeylGroup t.tag} (h : TwActsAs y u) (m : ℕ) :
    TwActsAs (y ^ m) (u ^ m) := by
  induction m with
  | zero => simpa using TwActsAs.one
  | succ m ih => rw [pow_succ, pow_succ]; exact ih.mul h

@[expose] def twTorsion (p : ℕ) : Subgroup (ModGL t.tag L) where
  carrier := {z | z ∈ D.torus ∧ z ^ p = 1}
  mul_mem' := by
    rintro a b ⟨haT, hap⟩ ⟨hbT, hbp⟩
    refine ⟨mul_mem haT hbT, ?_⟩
    have hc : Commute a b :=
      torusGroup_mul_comm (mem_twistedTorusOf.1 haT).1 (mem_twistedTorusOf.1 hbT).1
    rw [hc.mul_pow, hap, hbp, one_mul]
  one_mem' := ⟨one_mem _, one_pow _⟩
  inv_mem' := by
    rintro a ⟨haT, hap⟩
    exact ⟨inv_mem haT, by rw [inv_pow, hap, inv_one]⟩

theorem isPGroup_twTorsion (p : ℕ) [Fact p.Prime] : IsPGroup p (twTorsion D p) := fun g =>
  ⟨1, by
    rw [pow_one]
    exact Subtype.ext g.2.2⟩

theorem tw_mem_normalizer_twTorsion (p : ℕ) {y : ModGL t.tag L} (hy : y ∈ monomialSubgroup t.tag L)
    (hf : D.n * D.Φ y * D.n⁻¹ = y) :
    y ∈ Subgroup.normalizer ((twTorsion D p : Subgroup (ModGL t.tag L)) : Set (ModGL t.tag L)) := by
  have key : ∀ {y : ModGL t.tag L}, y ∈ monomialSubgroup t.tag L → D.n * D.Φ y * D.n⁻¹ = y →
      ∀ z ∈ twTorsion D p, y * z * y⁻¹ ∈ twTorsion D p := by
    intro y hy hf z hz
    refine ⟨tw_conj_mem_torus D hy hf hz.1, ?_⟩
    rw [conj_pow, hz.2]
    simp
  have hyinv : y⁻¹ ∈ monomialSubgroup t.tag L := inv_mem hy
  have hfinv : D.n * D.Φ y⁻¹ * D.n⁻¹ = y⁻¹ := by
    rw [map_inv]
    calc D.n * (D.Φ y)⁻¹ * D.n⁻¹ = (D.n * D.Φ y * D.n⁻¹)⁻¹ := by group
      _ = y⁻¹ := by rw [hf]
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨fun hz => key hy hf z hz, fun hz => ?_⟩
  have h := key hyinv hfinv _ hz
  simpa [mul_assoc] using h

theorem weylTuple_eq_of_pow_eq {u : WeylGroup t.tag} {p m : ℕ} [hp : Fact p.Prime] (hup : u ^ p = 1)
    (hm : ¬ p ∣ m) {β : Fin t.tag.rank → Lˣ} (h : weylTuple (u ^ m) β = β) :
    weylTuple u β = β := by
  have hm0 : (m : ZMod p) ≠ 0 := fun h0 => hm ((ZMod.natCast_eq_zero_iff m p).1 h0)
  set k := ((m : ZMod p)⁻¹).val with hk
  have hmk : ((m * k : ℕ) : ZMod p) = 1 := by
    rw [Nat.cast_mul, hk, ZMod.natCast_zmod_val, mul_inv_cancel₀ hm0]
  have hmk' : (m * k) % p = 1 := by
    have := (ZMod.natCast_eq_natCast_iff' (m * k) 1 p).1 (by simpa using hmk)
    rwa [Nat.mod_eq_of_lt hp.out.one_lt] at this
  have hu1 : u ^ (m * k) = u := by
    have h1 := Nat.div_add_mod (m * k) p
    rw [hmk'] at h1
    rw [← h1, pow_add, pow_mul, hup, one_pow, one_mul, pow_one]
  have hu1' : u = (u ^ m) ^ k := by rw [← pow_mul, hu1]
  have hfix : ∀ j : ℕ, weylTuple ((u ^ m) ^ j) β = β := by
    intro j
    induction j with
    | zero => simp [weylTuple_one]
    | succ j ih => rw [pow_succ, ← weylTuple_weylTuple, h, ih]
  rw [hu1']
  exact hfix k

theorem tw_rootDiagUnit_mem_torus {Fr : L →+* L} (hΦ : D.Φ = twistHom t L Fr) {w : WeylGroup t.tag}
    (hn : D.n = canonicalRep (coxeterSystem t.tag) L w)
    {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hv : ∀ x, w • permLattice t.perm x = M *ᵥ x) {β : Fin t.tag.rank → Lˣ}
    (hβ : β ∈ fixedCharTuples M Fr) : rootDiagUnit t.tag β ∈ D.torus := by
  have h := twistedTorusOf_twistHom_eq_map t Fr w M hv
  have : rootDiagUnit t.tag β ∈ twistedTorusOf (canonicalRep (coxeterSystem t.tag) L w)
      (twistHom t L Fr) := by
    rw [h]
    exact ⟨β, hβ, rfl⟩
  have e : D.torus = twistedTorusOf (canonicalRep (coxeterSystem t.tag) L w) (twistHom t L Fr) := by
    show twistedTorusOf D.n D.Φ = _
    rw [hn, hΦ]
  rw [e]
  exact this

theorem tw_exists_noncomm_pSubgroup [Finite D.model] {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom t L Fr) {w : WeylGroup t.tag}
    (hn : D.n = canonicalRep (coxeterSystem t.tag) L w)
    {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hv : ∀ x, w • permLattice t.perm x = M *ᵥ x) {N : ℕ} (hN0 : N ≠ 0) (hpow : M ^ N = 1)
    {p : ℕ} [hp : Fact p.Prime] {u : WeylGroup t.tag} (hu : w * weylTwist t u = u * w)
    (hup : u ^ p = 1) {β : Fin t.tag.rank → Lˣ} (hβ : β ∈ fixedCharTuples M Fr)
    (hβp : ∀ i, β i ^ p = 1) (hβu : weylTuple u β ≠ β) :
    ∃ (Q : Subgroup (ModGL t.tag L)) (x y : ModGL t.tag L), IsPGroup p Q ∧ x ∈ Q ∧ y ∈ Q ∧
      x ∈ D.model ∧ y ∈ D.model ∧ x * y ≠ y * x := by
  obtain ⟨ŷ, hmon, hfix, hact⟩ := tw_exists_lift D hq hFr hΦ hn hv hN0 hpow hu
  have hŷM : ŷ ∈ D.model := tw_mem_model D hmon hfix
  have hord : orderOf ŷ ≠ 0 := by
    have : orderOf (⟨ŷ, hŷM⟩ : D.model) ≠ 0 := (orderOf_pos _).ne'
    rwa [← Subgroup.orderOf_coe] at this
  obtain ⟨a, m, hm, hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord p hp.out.ne_one
  have hm0 : m ≠ 0 := fun h0 => hord (by rw [hmeq, h0, mul_zero])
  set y := ŷ ^ m with hy
  have hyM : y ∈ D.model := pow_mem hŷM m
  have hymon : y ∈ monomialSubgroup t.tag L := pow_mem hmon m
  have hyf : D.n * D.Φ y * D.n⁻¹ = y := (LangDatum.mem_model D).1 hyM |>.2
  have hyord : orderOf y = p ^ a := by
    rw [hy, orderOf_pow_of_dvd hm0 ⟨p ^ a, by rw [hmeq, mul_comm]⟩, hmeq,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hyact : TwActsAs y (u ^ m) := hact.pow m
  have hx : rootDiagUnit t.tag β ∈ D.torus := tw_rootDiagUnit_mem_torus D hΦ hn hv hβ
  have hxp : rootDiagUnit t.tag β ^ p = 1 := by
    have hpow' : rootDiagUnit t.tag (β ^ p) = rootDiagUnit t.tag β ^ p :=
      map_pow (rootDiagUnitHom t.tag L) β p
    rw [← hpow']
    have : β ^ p = 1 := funext fun i => hβp i
    rw [this]
    exact rootDiagUnit_one
  have hy3 : IsPGroup p (Subgroup.zpowers y) := by
    refine IsPGroup.of_card_dvd_pow (n := a) ?_
    rw [Nat.card_zpowers, hyord]
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer
      ((twTorsion D p : Subgroup (ModGL t.tag L)) : Set (ModGL t.tag L)) :=
    Subgroup.zpowers_le.2 (tw_mem_normalizer_twTorsion D p hymon hyf)
  refine ⟨Subgroup.zpowers y ⊔ twTorsion D p, rootDiagUnit t.tag β, y,
    hy3.to_sup_of_normal_right' (isPGroup_twTorsion D p) hnorm,
    Subgroup.mem_sup_right ⟨hx, hxp⟩, Subgroup.mem_sup_left (Subgroup.mem_zpowers y),
    D.torus_le_model hx, hyM, fun hxy => hβu ?_⟩
  have h1 : y * rootDiagUnit t.tag β * y⁻¹ = rootDiagUnit t.tag β := by
    rw [← hxy, mul_assoc, mul_inv_cancel, mul_one]
  rw [hyact β] at h1
  exact weylTuple_eq_of_pow_eq hup hm
    (CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := t.tag) (K := L) h1)

theorem tw_exists_noncomm_pSubgroup_Γ [Finite D.model] {Fr : L →+* L} {q : ℕ} (hq : 2 ≤ q)
    (hFr : ∀ c, Fr c = c ^ q) (hΦ : D.Φ = twistHom t L Fr) {w : WeylGroup t.tag}
    (hn : D.n = canonicalRep (coxeterSystem t.tag) L w)
    {M : Matrix (Fin t.tag.rank) (Fin t.tag.rank) ℤ}
    (hv : ∀ x, w • permLattice t.perm x = M *ᵥ x) {N : ℕ} (hN0 : N ≠ 0) (hpow : M ^ N = 1)
    {p : ℕ} [hp : Fact p.Prime] {a b s : WeylGroup t.tag}
    (ha : w * weylTwist t a = a * w) (hb : w * weylTwist t b = b * w)
    (hs : w * weylTwist t s = s * w) (hup : ⁅a, b⁆ ^ p = 1)
    {β : Fin t.tag.rank → Lˣ} (hβ : β ∈ fixedCharTuples M Fr) (hβp : ∀ i, β i ^ p = 1)
    (hγ : weylTuple ⁅a, b⁆ (weylTuple s β * β⁻¹) ≠ weylTuple s β * β⁻¹) :
    ∃ (Q : Subgroup (ModGL t.tag L)) (x y : ModGL t.tag L), IsPGroup p Q ∧ x ∈ Q ∧ y ∈ Q ∧
      x ∈ D.Γ ∧ y ∈ D.Γ ∧ x * y ≠ y * x := by
  obtain ⟨ya, hmona, hfixa, hacta⟩ := tw_exists_lift D hq hFr hΦ hn hv hN0 hpow ha
  obtain ⟨yb, hmonb, hfixb, hactb⟩ := tw_exists_lift D hq hFr hΦ hn hv hN0 hpow hb
  obtain ⟨ys, hmons, hfixs, hacts⟩ := tw_exists_lift D hq hFr hΦ hn hv hN0 hpow hs
  have hŷΓ : ⁅ya, yb⁆ ∈ D.Γ :=
    tw_commutator_mem_Γ D (tw_mem_model D hmona hfixa) (tw_mem_model D hmonb hfixb)
  have hŷM : ⁅ya, yb⁆ ∈ D.model := tw_Γ_le_model D hŷΓ
  have hŷact : TwActsAs ⁅ya, yb⁆ ⁅a, b⁆ := hacta.commutator hactb
  have hŷmon : ⁅ya, yb⁆ ∈ monomialSubgroup t.tag L := by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hmona hmonb) (inv_mem hmona)) (inv_mem hmonb)
  have hord : orderOf ⁅ya, yb⁆ ≠ 0 := by
    have : orderOf (⟨⁅ya, yb⁆, hŷM⟩ : D.model) ≠ 0 := (orderOf_pos _).ne'
    rwa [← Subgroup.orderOf_coe] at this
  obtain ⟨c, m, hm, hmeq⟩ := Nat.exists_eq_pow_mul_and_not_dvd hord p hp.out.ne_one
  have hm0 : m ≠ 0 := fun h0 => hord (by rw [hmeq, h0, mul_zero])
  set y := ⁅ya, yb⁆ ^ m with hy
  have hyΓ : y ∈ D.Γ := pow_mem hŷΓ m
  have hyM : y ∈ D.model := pow_mem hŷM m
  have hymon : y ∈ monomialSubgroup t.tag L := pow_mem hŷmon m
  have hyf : D.n * D.Φ y * D.n⁻¹ = y := (LangDatum.mem_model D).1 hyM |>.2
  have hyord : orderOf y = p ^ c := by
    rw [hy, orderOf_pow_of_dvd hm0 ⟨p ^ c, by rw [hmeq, mul_comm]⟩, hmeq,
      Nat.mul_div_cancel _ (Nat.pos_of_ne_zero hm0)]
  have hyact : TwActsAs y (⁅a, b⁆ ^ m) := hŷact.pow m
  have hdβ : rootDiagUnit t.tag β ∈ D.torus := tw_rootDiagUnit_mem_torus D hΦ hn hv hβ
  have hdβp : rootDiagUnit t.tag β ^ p = 1 := by
    have hpow' : rootDiagUnit t.tag (β ^ p) = rootDiagUnit t.tag β ^ p :=
      map_pow (rootDiagUnitHom t.tag L) β p
    rw [← hpow']
    have : β ^ p = 1 := funext fun i => hβp i
    rw [this]
    exact rootDiagUnit_one
  set x := ⁅ys, rootDiagUnit t.tag β⁆ with hx
  have hxΓ : x ∈ D.Γ :=
    tw_commutator_mem_Γ D (tw_mem_model D hmons hfixs) (D.torus_le_model hdβ)
  have hxe : x = rootDiagUnit t.tag (weylTuple s β * β⁻¹) := by
    rw [hx, commutatorElement_def, hacts β, rootDiagUnit_mul, rootDiagUnit_inv]
  have hxT : x ∈ D.torus := by
    rw [hx, commutatorElement_def]
    exact mul_mem (tw_conj_mem_torus D hmons hfixs hdβ) (inv_mem hdβ)
  have hc : Commute (ys * rootDiagUnit t.tag β * ys⁻¹) (rootDiagUnit t.tag β)⁻¹ :=
    torusGroup_mul_comm (mem_twistedTorusOf.1 (tw_conj_mem_torus D hmons hfixs hdβ)).1
      (mem_twistedTorusOf.1 (inv_mem hdβ)).1
  have hxp : x ^ p = 1 := by
    rw [hx, commutatorElement_def, hc.mul_pow, conj_pow, hdβp, inv_pow, hdβp]
    simp
  have hy3 : IsPGroup p (Subgroup.zpowers y) := by
    refine IsPGroup.of_card_dvd_pow (n := c) ?_
    rw [Nat.card_zpowers, hyord]
  have hnorm : Subgroup.zpowers y ≤ Subgroup.normalizer
      ((twTorsion D p : Subgroup (ModGL t.tag L)) : Set (ModGL t.tag L)) :=
    Subgroup.zpowers_le.2 (tw_mem_normalizer_twTorsion D p hymon hyf)
  refine ⟨Subgroup.zpowers y ⊔ twTorsion D p, x, y,
    hy3.to_sup_of_normal_right' (isPGroup_twTorsion D p) hnorm,
    Subgroup.mem_sup_right ⟨hxT, hxp⟩, Subgroup.mem_sup_left (Subgroup.mem_zpowers y),
    hxΓ, hyΓ, fun hxy => hγ ?_⟩
  have h1 : y * x * y⁻¹ = x := by
    rw [← hxy, mul_assoc, mul_inv_cancel, mul_one]
  rw [hxe] at h1
  rw [hyact] at h1
  exact weylTuple_eq_of_pow_eq hup hm
    (CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := t.tag) (K := L) h1)

end Witness

end CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
