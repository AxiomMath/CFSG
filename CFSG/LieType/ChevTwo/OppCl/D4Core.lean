module

public import CFSG.LieType.ChevTwo.OppCl.D4Lift
public import CFSG.LieType.ChevTwo.OppositeFixedExcTri
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer

set_option linter.unusedSectionVars false

public section

namespace CFSG.LieType.ChevTwo.Semi

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Chevalley.EvenOddRadical CFSG.Open CFSG.LieType.BorelTits
  CFSG.HardMathSupport.Lang.D4Three CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

theorem d4_exists_mem_of_conj_sylow_le {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) {H : Subgroup G} (hS : (S : Subgroup G) ≤ H) (g : G)
    (hgS : ∀ s ∈ (S : Subgroup G), g * s * g⁻¹ ∈ H) :
    ∃ x ∈ H, ∀ s : G, s ∈ (S : Subgroup G) ↔
      (x⁻¹ * g) * s * (x⁻¹ * g)⁻¹ ∈ (S : Subgroup G) := by
  have hmemg : ∀ y : G, y ∈ ((g • S : Sylow p G) : Subgroup G) ↔
      g⁻¹ * y * g ∈ (S : Subgroup G) := by
    intro y
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp [MulAut.conj_symm_apply]
  have hgS' : ((g • S : Sylow p G) : Subgroup G) ≤ H := by
    intro y hy
    have := hgS _ ((hmemg y).1 hy)
    simpa [mul_assoc] using this
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq H (S.subtype hS) ((g • S).subtype hgS')
  have hmem : ∀ z : H, ((z : G) ∈ ((g • S : Sylow p G) : Subgroup G)) ↔
      (((x⁻¹ * z * x : H)) : G) ∈ (S : Subgroup G) := by
    intro z
    have h1 : z ∈ (((g • S).subtype hgS' : Sylow p H) : Subgroup H) ↔
        z ∈ ((x • S.subtype hS : Sylow p H) : Subgroup H) := by rw [hx]
    rw [Sylow.coe_subtype, Subgroup.mem_subgroupOf] at h1
    rw [h1, Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem,
      Sylow.coe_subtype, Subgroup.mem_subgroupOf]
    simp [MulAut.conj_symm_apply]
  refine ⟨(x : G), x.2, fun s => ⟨fun hs => ?_, fun hs => ?_⟩⟩
  · have hz : g * s * g⁻¹ ∈ H := hgS s hs
    have h1 := (hmem ⟨g * s * g⁻¹, hz⟩).1 ((hmemg _).2 (by simpa [mul_assoc] using hs))
    simpa [mul_assoc] using h1
  · have hxH : (x : G) ∈ H := x.2
    have ht : ((x : G)⁻¹ * g) * s * ((x : G)⁻¹ * g)⁻¹ ∈ (S : Subgroup G) := hs
    have hz : (x : G) * (((x : G)⁻¹ * g) * s * ((x : G)⁻¹ * g)⁻¹) * (x : G)⁻¹ ∈ H :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hxH (hS ht)) (Subgroup.inv_mem _ hxH)
    have h1 := (hmem ⟨_, hz⟩).2 (by simpa [mul_assoc] using ht)
    have h2 := (hmemg _).1 h1
    simpa [mul_assoc] using h2

section Cert

variable
    {K : Type} [Field K] [Finite K] [CharP K 2]

theorem mem_parG_of_unipotentPair {J : Set (Fin Tag.D4.rank)} {g : adjointGroup Tag.D4 K}
    {A α : MulAut (adjointGroup Tag.D4 K)} (hA : A ∈ unipotentPairAut Tag.D4 K)
    (hα : α = MulAut.conj g * A)
    (hQR : (radG Tag.D4 K J).map α.toMonoidHom = radG Tag.D4 K J)
    (hNQ : Subgroup.normalizer ((radG Tag.D4 K J : Subgroup ↥(adjointGroup Tag.D4 K)) :
      Set ↥(adjointGroup Tag.D4 K)) = parG Tag.D4 K J) :
    g ∈ parG Tag.D4 K J := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfin : Finite (ModGL Tag.D4 K) := finite_modGL
  set UC : Subgroup (adjointGroup Tag.D4 K) :=
    (posUnipotent Tag.D4 K).subgroupOf (adjointGroup Tag.D4 K) with hUC
  have hAU : UC.map A.toMonoidHom = UC := hA.1
  have hQ1 : ((radG Tag.D4 K J).map A.toMonoidHom).map (MulAut.conj g).toMonoidHom =
      radG Tag.D4 K J := by
    rw [← map_toMonoidHom_mul_mulAut, ← hα]; exact hQR
  have hQ2 : (radG Tag.D4 K J).map (MulAut.conj g)⁻¹.toMonoidHom =
      (radG Tag.D4 K J).map A.toMonoidHom := map_inv_toMonoidHom_of_map_eq hQ1
  have hP1 : (parG Tag.D4 K J).map A.toMonoidHom = (parG Tag.D4 K J).map (MulAut.conj g)⁻¹.toMonoidHom := by
    rw [← hNQ, Subgroup.map_equiv_normalizer_eq, Subgroup.map_equiv_normalizer_eq, hQ2]
  have hUP : UC ≤ parG Tag.D4 K J := fun x hx =>
    Subgroup.mem_subgroupOf.2 (posUnipotent_le_parabolicSubgroup J (Subgroup.mem_subgroupOf.1 hx))
  have hgU : ∀ u ∈ UC, g * u * g⁻¹ ∈ parG Tag.D4 K J := by
    intro u hu
    rw [← hAU] at hu
    obtain ⟨u', hu', rfl⟩ := hu
    have h1 : A u' ∈ (parG Tag.D4 K J).map A.toMonoidHom := ⟨u', hUP hu', rfl⟩
    rw [hP1] at h1
    obtain ⟨p', hp', hpe⟩ := h1
    have : p' = MulAut.conj g (A u') := by
      rw [← hpe]; simp; group
    rw [this] at hp'
    simpa [MulAut.conj_apply] using hp'
  obtain ⟨w₀, hw₀⟩ := Finite.exists_max (coxeterSystem Tag.D4).length
  obtain ⟨S, hS⟩ := (exceptional_ordinary_Sylow_opposition Tag.D4 K 2 w₀ hw₀).1
  have hSU : (S : Subgroup (adjointGroup Tag.D4 K)) = UC := hS
  obtain ⟨x, hx, hxn⟩ := d4_exists_mem_of_conj_sylow_le S (H := parG Tag.D4 K J)
    (by rw [hSU]; exact hUP) g (fun s hs => hgU s (by rwa [hSU] at hs))
  have hnorm : x⁻¹ * g ∈ Subgroup.normalizer (UC : Set (adjointGroup Tag.D4 K)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro s
    rw [hSU] at hxn
    exact hxn s
  have hUle : posUnipotent Tag.D4 K ≤ adjointGroup Tag.D4 K := posUnipotent_le_adjointGroup
  have hN1 := mem_normalizer_map_subtype hnorm
  rw [hUC, Subgroup.map_subgroupOf_eq_of_le hUle] at hN1
  have hB := (borel_self_normalizers (τ := Tag.D4) (K := K)).1
  have hxg : ((x⁻¹ * g : adjointGroup Tag.D4 K) : ModGL Tag.D4 K) ∈
      adjointGroup Tag.D4 K ⊓ Subgroup.normalizer (posUnipotent Tag.D4 K : Set (ModGL Tag.D4 K)) :=
    Subgroup.mem_inf.2 ⟨(x⁻¹ * g).2, hN1⟩
  rw [hB] at hxg
  have hxgP : x⁻¹ * g ∈ parG Tag.D4 K J :=
    Subgroup.mem_subgroupOf.2 (le_sup_left (a := borelGroup Tag.D4 K) hxg)
  have := Subgroup.mul_mem _ hx hxgP
  simpa using this


theorem d4P_mul_weylElt_mul_inv (j : Fin Tag.D4.rank) :
    d4P K * weylElt Tag.D4 K j 1 * (d4P K)⁻¹ = weylElt Tag.D4 K (d4Rho j) 1 := by
  have h := twistHom_weylElt_one TwistTag.D4 K (RingHom.id K) j
  rw [twistHom_id_eq_conj] at h
  exact h

theorem d4P_pow_mul_weylElt_mul_inv (ε : ℕ) (j : Fin Tag.D4.rank) :
    d4P K ^ ε * weylElt Tag.D4 K j 1 * (d4P K ^ ε)⁻¹ =
      weylElt Tag.D4 K ((d4Rho ^ ε) j) 1 := by
  induction ε with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', pow_succ', mul_inv_rev]
    have : d4P K * d4P K ^ n * weylElt Tag.D4 K j 1 * ((d4P K ^ n)⁻¹ * (d4P K)⁻¹) =
        d4P K * (d4P K ^ n * weylElt Tag.D4 K j 1 * (d4P K ^ n)⁻¹) * (d4P K)⁻¹ := by group
    rw [this, ih, d4P_mul_weylElt_mul_inv]
    rfl

theorem d4_normalGraph_weylElt (σ : K ≃+* K) (ε : ℕ) (j : Fin Tag.D4.rank) :
    (((exactNormalAut Tag.D4 K 1 σ 0 * d4Graph K ε)
      ⟨weylElt Tag.D4 K j 1, weylElt_mem_adjointGroup j 1⟩ : adjointGroup Tag.D4 K) :
        ModGL Tag.D4 K) = weylElt Tag.D4 K ((d4Rho ^ ε) j) 1 := by
  rw [MulAut.mul_apply, coe_exactNormalAut_zero, rootDiagUnit_one, one_mul, inv_one, mul_one]
  show Units.map (entrywiseHom σ.toRingHom) (d4P K ^ ε * weylElt Tag.D4 K j 1 * (d4P K ^ ε)⁻¹) = _
  have hP : Units.map (entrywiseHom σ.toRingHom) (d4P K) = d4P K :=
    units_map_entrywiseHom_diagramMap σ.toRingHom
  rw [map_mul, map_mul, map_inv, map_pow, hP, entrywise_weylElt_one, d4P_pow_mul_weylElt_mul_inv]

theorem d4_stable_of_normalizes {J : Set (Fin Tag.D4.rank)} {g : adjointGroup Tag.D4 K}
    {σ : K ≃+* K} {ε : ℕ} {α : MulAut (adjointGroup Tag.D4 K)}
    (hα : α = MulAut.conj g * (exactNormalAut Tag.D4 K 1 σ 0 * d4Graph K ε))
    (hg : g ∈ parG Tag.D4 K J)
    (hQR : (radG Tag.D4 K J).map α.toMonoidHom = radG Tag.D4 K J)
    (hNQ : Subgroup.normalizer ((radG Tag.D4 K J : Subgroup ↥(adjointGroup Tag.D4 K)) :
      Set ↥(adjointGroup Tag.D4 K)) = parG Tag.D4 K J) :
    ∀ j ∈ J, (d4Rho ^ ε) j ∈ J := by
  set A := exactNormalAut Tag.D4 K 1 σ 0 * d4Graph K ε with hAdef
  have hgN : g ∈ Subgroup.normalizer ((radG Tag.D4 K J : Subgroup ↥(adjointGroup Tag.D4 K)) :
      Set ↥(adjointGroup Tag.D4 K)) := hNQ ▸ hg
  have hAr : (radG Tag.D4 K J).map A.toMonoidHom = radG Tag.D4 K J := by
    have h1 : ((radG Tag.D4 K J).map A.toMonoidHom).map (MulAut.conj g).toMonoidHom =
        radG Tag.D4 K J := by
      rw [← map_toMonoidHom_mul_mulAut, ← hα]; exact hQR
    have h2 : (radG Tag.D4 K J).map (MulAut.conj g).toMonoidHom = radG Tag.D4 K J :=
      map_conj_eq_of_mem_normalizer' hgN
    exact Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom)
      (fun a b h => (MulAut.conj g).injective h) (h1.trans h2.symm)
  have hAp : (parG Tag.D4 K J).map A.toMonoidHom = parG Tag.D4 K J := by
    rw [← hNQ, Subgroup.map_equiv_normalizer_eq, hAr]
  intro j hj
  have hn : (⟨weylElt Tag.D4 K j 1, weylElt_mem_adjointGroup j 1⟩ : adjointGroup Tag.D4 K) ∈
      parG Tag.D4 K J :=
    Subgroup.mem_subgroupOf.2 (weylElt_mem_parabolicSubgroup_iff.2 hj)
  have h1 : A ⟨weylElt Tag.D4 K j 1, weylElt_mem_adjointGroup j 1⟩ ∈ parG Tag.D4 K J := by
    rw [← hAp]; exact ⟨_, hn, rfl⟩
  have h2 := Subgroup.mem_subgroupOf.1 h1
  rw [hAdef, d4_normalGraph_weylElt] at h2
  exact weylElt_mem_parabolicSubgroup_iff.1 h2

theorem d4_stable_of_pow {J : Set (Fin Tag.D4.rank)} {ε : ℕ} (hε : ε % 3 ≠ 0)
    (h : ∀ j ∈ J, (d4Rho ^ ε) j ∈ J) : ∀ i, d4Rho i ∈ J ↔ i ∈ J := by
  have h3 : ∀ j, d4Rho (d4Rho (d4Rho j)) = j := fun j => by
    have := congrArg (fun f : Equiv.Perm (Fin Tag.D4.rank) => f j) d4Rho_pow_three'
    simpa [pow_succ] using this
  have he : d4Rho ^ ε = d4Rho ^ (ε % 3) := by
    conv_lhs => rw [← Nat.mod_add_div ε 3, pow_add, pow_mul, d4Rho_pow_three', one_pow, mul_one]
  have hfwd : ∀ j ∈ J, d4Rho j ∈ J := by
    have hlt : ε % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have : ε % 3 = 1 ∨ ε % 3 = 2 := by omega
    rw [he] at h
    rcases this with h1 | h1
    · rw [h1, pow_one] at h; exact h
    · rw [h1] at h
      intro j hj
      have h2 := h _ (h _ hj)
      have : (d4Rho ^ 2) ((d4Rho ^ 2) j) = d4Rho j := by
        have e : (d4Rho ^ 2) ((d4Rho ^ 2) j) = d4Rho (d4Rho (d4Rho (d4Rho j))) := by
          simp [pow_succ]
        rw [e, h3]
      rw [this] at h2
      exact h2
  intro i
  refine ⟨fun hi => ?_, hfwd i⟩
  have := hfwd _ (hfwd _ hi)
  rwa [h3] at this


theorem d4_le_normalizer_of_conj_mem {G : Type*} [Group G] {Z R : Subgroup G}
    (h : ∀ z ∈ Z, ∀ r ∈ R, z * r * z⁻¹ ∈ R) : Z ≤ Subgroup.normalizer (R : Set G) := by
  intro z hz
  rw [Subgroup.mem_normalizer_iff]
  intro r
  refine ⟨h z hz r, fun hr => ?_⟩
  have := h z⁻¹ (Z.inv_mem hz) _ hr
  simpa [mul_assoc] using this

theorem d4P_mem_normalizer_radical {J : Set (Fin Tag.D4.rank)}
    (hJ : ∀ i, d4Rho i ∈ J ↔ i ∈ J) :
    d4P K ∈ Subgroup.normalizer (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) := by
  have h := diagramMap_mem_normalizer_levelRadical (t := TwistTag.D4) (K := K) (A := J) hJ 1
  have h2 : levelRadical TwistTag.D4.tag K J 1 = parabolicRadical Tag.D4 K J :=
    levelRadical_one (τ := TwistTag.D4.tag) (K := K) (J := J)
  rw [h2] at h
  exact h

theorem d4P_mem_normalizer_parabolicSubgroup {J : Set (Fin Tag.D4.rank)}
    (hJ : ∀ i, d4Rho i ∈ J ↔ i ∈ J) :
    d4P K ∈ Subgroup.normalizer (parabolicSubgroup Tag.D4 K J : Set (ModGL Tag.D4 K)) := by
  have hPQ := d4P_mem_normalizer_radical (K := K) hJ
  have hPC := d4P_mem_normalizer_adjointGroup (K := K)
  have e := adjointGroup_inf_normalizer_parabolicRadical (τ := Tag.D4) (K := K) J
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [← e, Subgroup.mem_inf, Subgroup.mem_inf]
  have h1 := Subgroup.mem_normalizer_iff.1 hPC x
  have h2 : x ∈ Subgroup.normalizer (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) ↔
      d4P K * x * (d4P K)⁻¹ ∈ Subgroup.normalizer
        (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) := by
    constructor
    · intro hx
      exact mul_mem (mul_mem hPQ hx) (inv_mem hPQ)
    · intro hx
      have := mul_mem (mul_mem (inv_mem hPQ) hx) hPQ
      simpa [mul_assoc] using this
  rw [h1, h2]

theorem d4P_conj_mem_levi {J : Set (Fin Tag.D4.rank)} (hJ : ∀ i, d4Rho i ∈ J ↔ i ∈ J)
    {h : ModGL Tag.D4 K} (hh : h ∈ parabolicLevi Tag.D4 K J) :
    d4P K * h * (d4P K)⁻¹ ∈ parabolicLevi Tag.D4 K J := by
  have hle : parabolicLevi Tag.D4 K J ≤
      (parabolicLevi Tag.D4 K J).comap (MulAut.conj (d4P K)).toMonoidHom := by
    refine sup_le (fun b hb => ?_) ((Subgroup.closure_le _).2 ?_)
    · rw [Subgroup.mem_comap]
      have h1 := map_twistHom_torusGroup TwistTag.D4 K (σ := RingHom.id K) Function.surjective_id
      rw [twistHom_id_eq_conj] at h1
      have hmem : (MulEquiv.toMonoidHom (MulAut.conj (diagramMap TwistTag.D4 K))) b ∈
          torusGroup TwistTag.D4.tag K := by
        rw [← h1]
        exact ⟨b, hb, rfl⟩
      exact Subgroup.mem_sup_left hmem
    · rintro _ ⟨j, hj, c, rfl | rfl⟩
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        change d4P K * xUnit Tag.D4 K j c * (d4P K)⁻¹ ∈ _
        rw [show d4P K * xUnit Tag.D4 K j c * (d4P K)⁻¹ = xUnit Tag.D4 K (d4Rho j) c from
          diagramMap_mul_xUnit_mul_inv TwistTag.D4 K j c]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨d4Rho j, (hJ j).2 hj, c, Or.inl rfl⟩)
      · rw [SetLike.mem_coe, Subgroup.mem_comap]
        change d4P K * yUnit Tag.D4 K j c * (d4P K)⁻¹ ∈ _
        rw [show d4P K * yUnit Tag.D4 K j c * (d4P K)⁻¹ = yUnit Tag.D4 K (d4Rho j) c from
          diagramMap_mul_yUnit_mul_inv TwistTag.D4 K j c]
        exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨d4Rho j, (hJ j).2 hj, c, Or.inr rfl⟩)
  exact hle hh

theorem d4P_mem_normalizer_levi {J : Set (Fin Tag.D4.rank)} (hJ : ∀ i, d4Rho i ∈ J ↔ i ∈ J) :
    d4P K ∈ Subgroup.normalizer (parabolicLevi Tag.D4 K J : Set (ModGL Tag.D4 K)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => d4P_conj_mem_levi hJ hx, fun hx => ?_⟩
  have h1 := d4P_conj_mem_levi hJ (d4P_conj_mem_levi hJ hx)
  have e : d4P K * (d4P K * (d4P K * x * (d4P K)⁻¹) * (d4P K)⁻¹) * (d4P K)⁻¹ = x := by
    have h3 : d4P K * d4P K * d4P K = 1 := by rw [← pow_three']; exact d4P_pow_three
    calc _ = (d4P K * d4P K * d4P K) * x * (d4P K * d4P K * d4P K)⁻¹ := by group
      _ = x := by rw [h3]; group
  rwa [e] at h1

theorem fieldAut_mem_sup_zpowers {H : Subgroup (ModGL Tag.D4 K)}
    (hH : ∀ σ : RingAut K, ∀ h ∈ H, fieldAutHom Tag.D4 K σ h ∈ H) (σ : RingAut K)
    {x : ModGL Tag.D4 K} (hx : x ∈ H ⊔ Subgroup.zpowers (d4P K)) :
    fieldAutHom Tag.D4 K σ x ∈ H ⊔ Subgroup.zpowers (d4P K) := by
  have hle : H ⊔ Subgroup.zpowers (d4P K) ≤
      (H ⊔ Subgroup.zpowers (d4P K)).comap (fieldAutHom Tag.D4 K σ).toMonoidHom := by
    refine sup_le (fun y hy => ?_) (Subgroup.zpowers_le.2 ?_)
    · exact Subgroup.mem_sup_left (hH σ y hy)
    · rw [Subgroup.mem_comap]
      change fieldAutHom Tag.D4 K σ (d4P K) ∈ _
      rw [fieldAut_d4P]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
  exact hle hx

theorem d4P_pow_eq_one_of_mem {i : ℕ} (h : d4P K ^ i ∈ adjointGroup Tag.D4 K) :
    d4P K ^ i = 1 := by
  have h1 : MulAut.conj (⟨d4P K ^ i, h⟩ : adjointGroup Tag.D4 K)⁻¹ *
      (exactNormalAut Tag.D4 K 1 (1 : K ≃+* K) 0 * d4Graph K i) = 1 := by
    refine MulEquiv.ext fun x => Subtype.ext ?_
    rw [exactNormalAut_one_one_zero]
    simp only [MulAut.mul_apply, MulAut.one_apply, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv, coe_d4Graph]
    change (d4P K ^ i)⁻¹ * (d4P K ^ i * (x : ModGL Tag.D4 K) * (d4P K ^ i)⁻¹) *
      ((d4P K ^ i)⁻¹)⁻¹ = (x : ModGL Tag.D4 K)
    group
  exact (eq_one_of_conj_normal_form_eq_one h1).2.2


theorem exists_conj_into_levi_P (J : Set (Fin Tag.D4.rank)) (hJ : ∀ i, d4Rho i ∈ J ↔ i ∈ J)
    {T : Subgroup (GamL Tag.D4 K)}
    (hT : ∀ s ∈ T, s.left ∈ parabolicSubgroup Tag.D4 K J ⊔ Subgroup.zpowers (d4P K))
    (hodd : ¬ 2 ∣ Nat.card T) :
    ∃ y ∈ parabolicRadical Tag.D4 K J, ∀ s ∈ T,
      ((SemidirectProduct.inl y : GamL Tag.D4 K) * s * (SemidirectProduct.inl y)⁻¹).left ∈
        parabolicLevi Tag.D4 K J ⊔ Subgroup.zpowers (d4P K) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfinM : Finite (ModGL Tag.D4 K) := finite_modGL
  have hfinσ : Finite (RingAut K) :=
    Finite.of_injective (fun σ : RingAut K => (σ : K → K)) fun a b h => RingEquiv.ext (congrFun h)
  have hfinΓ : Finite (GamL Tag.D4 K) :=
    Finite.of_equiv (ModGL Tag.D4 K × RingAut K) (SemidirectProduct.equivProd).symm
  obtain ⟨hQP, -, -, -, hQM, -, hdec, -⟩ := parabolic_root_radical_Levi_factors Tag.D4 K J
  have hQ2 : IsPGroup 2 (parabolicRadical Tag.D4 K J) :=
    (isPGroup_posUnipotent 2 Tag.D4).to_le (parabolicRadical_le_posUnipotent J)
  have hPQ := d4P_mem_normalizer_radical (K := K) hJ
  have hPP := d4P_mem_normalizer_parabolicSubgroup (K := K) hJ
  have hPM := d4P_mem_normalizer_levi (K := K) hJ
  let Ppar : Subgroup (GamL Tag.D4 K) :=
    gamSub (parabolicSubgroup Tag.D4 K J ⊔ Subgroup.zpowers (d4P K))
      fun σ _ hh => fieldAut_mem_sup_zpowers (fun σ h hh => fieldAut_mem_parabolicSubgroup σ hh) σ hh
  let Mlev : Subgroup (GamL Tag.D4 K) :=
    gamSub (parabolicLevi Tag.D4 K J ⊔ Subgroup.zpowers (d4P K))
      fun σ _ hh => fieldAut_mem_sup_zpowers (fun σ h hh => fieldAut_mem_parabolicLevi σ hh) σ hh
  let Qrad : Subgroup (GamL Tag.D4 K) := (parabolicRadical Tag.D4 K J).map SemidirectProduct.inl
  have hQrad2 : IsPGroup 2 Qrad := hQ2.map _
  have hQradPpar : Qrad ≤ Ppar := by
    rintro _ ⟨q, hq, rfl⟩
    exact Subgroup.mem_sup_left (hQP hq)
  have hPparLe : parabolicSubgroup Tag.D4 K J ⊔ Subgroup.zpowers (d4P K) ≤
      Subgroup.normalizer (parabolicRadical Tag.D4 K J : Set (ModGL Tag.D4 K)) :=
    sup_le (parabolicSubgroup_le_normalizer_parabolicRadical J) (Subgroup.zpowers_le.2 hPQ)
  have hPparN : Ppar ≤ Subgroup.normalizer (Qrad : Set (GamL Tag.D4 K)) := by
    refine d4_le_normalizer_of_conj_mem fun s hs y hy => ?_
    obtain ⟨q, hq, rfl⟩ := hy
    rw [conj_inl]
    refine ⟨conjAct Tag.D4 K s q, ?_, rfl⟩
    rw [conjAct_apply]
    exact (Subgroup.mem_normalizer_iff.1 (hPparLe hs) _).1
      (fieldAut_mem_parabolicRadical s.right hq)
  have hQradMlev : Qrad ⊓ Mlev = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    obtain ⟨⟨q, hq, rfl⟩, hxM⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨m, hm, i, hmi⟩ := (mem_sup_zpowers_d4P_iff hPM).1
      (show (SemidirectProduct.inl q : GamL Tag.D4 K).left ∈
        parabolicLevi Tag.D4 K J ⊔ Subgroup.zpowers (d4P K) from hxM)
    have hqm : q = m * d4P K ^ i := by simpa using hmi
    have hmC : m ∈ adjointGroup Tag.D4 K :=
      parabolicSubgroup_le_adjointGroup Tag.D4 K J (parabolicLevi_le_parabolicSubgroup J hm)
    have hqC : q ∈ adjointGroup Tag.D4 K :=
      parabolicSubgroup_le_adjointGroup Tag.D4 K J (hQP hq)
    have hPi : d4P K ^ i ∈ adjointGroup Tag.D4 K := by
      have : d4P K ^ i = m⁻¹ * q := by rw [hqm]; group
      rw [this]
      exact mul_mem (inv_mem hmC) hqC
    have h1 := d4P_pow_eq_one_of_mem hPi
    rw [h1, mul_one] at hqm
    have : q = 1 := Subgroup.mem_bot.1 (hQM ▸ Subgroup.mem_inf.2 ⟨hq, hqm ▸ hm⟩)
    rw [this, map_one]
    exact Subgroup.one_mem _
  have hdec' : ∀ g ∈ Ppar, ∃ q ∈ Qrad, ∃ m ∈ Mlev, q * m = g := by
    intro g hg
    obtain ⟨x, hxP, i, hxi⟩ := (mem_sup_zpowers_d4P_iff hPP).1
      (show g.left ∈ parabolicSubgroup Tag.D4 K J ⊔ Subgroup.zpowers (d4P K) from hg)
    obtain ⟨qm, ⟨hq, hm, hx⟩, -⟩ := hdec x hxP
    refine ⟨SemidirectProduct.inl qm.1, ⟨qm.1, hq, rfl⟩,
      ⟨qm.2 * d4P K ^ i, g.right⟩, ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hm)
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i))
    · refine SemidirectProduct.ext ?_ ?_
      · rw [SemidirectProduct.mul_left, SemidirectProduct.left_inl, SemidirectProduct.right_inl,
          map_one, MulAut.one_apply, hxi, hx]
        change qm.1 * (qm.2 * d4P K ^ i) = qm.1 * qm.2 * d4P K ^ i
        rw [mul_assoc]
      · rw [SemidirectProduct.mul_right, SemidirectProduct.right_inl, one_mul]
  obtain ⟨y, hyQ, hyM⟩ := exists_conj_le_of_complement (p := 2) (P := Ppar) (Q := Qrad)
    (M := Mlev) hQrad2 hQradPpar hPparN hQradMlev hdec' (fun s hs => hT s hs) hodd
  obtain ⟨y₀, hy₀, rfl⟩ := hyQ
  refine ⟨y₀, hy₀, fun s hs => ?_⟩
  exact hyM (Subgroup.mem_map_of_mem _ hs)


theorem d4_core_tail {J : Set (Fin Tag.D4.rank)}
    {R : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} {T : Subgroup (GamL Tag.D4 K)}
    (hT1 : ∀ α ∈ R, ∃ s ∈ T, ∀ h : adjointGroup Tag.D4 K,
      (α h : ModGL Tag.D4 K) = conjAct Tag.D4 K s h)
    (hT2 : ∀ s ∈ T, ∃ α ∈ R, ∀ h : adjointGroup Tag.D4 K,
      (α h : ModGL Tag.D4 K) = conjAct Tag.D4 K s h)
    (hC : autCentralizer R ≤ parG Tag.D4 K J)
    {w₁ : adjointGroup Tag.D4 K} (hwC : w₁ ∈ autCentralizer R) (hwQ : w₁ ∈ radG Tag.D4 K J)
    (hw1 : w₁ ≠ 1) {y₀ : ModGL Tag.D4 K} (hy₀ : y₀ ∈ parabolicRadical Tag.D4 K J)
    (hdual : ∀ u ∈ parabolicRadical Tag.D4 K J, u ≠ 1 →
      (∀ s ∈ T.map (MulAut.conj (SemidirectProduct.inl y₀ : GamL Tag.D4 K)).toMonoidHom,
        conjAct Tag.D4 K s u = u) →
      ∃ v ∈ oppRadical Tag.D4 K J, v ≠ 1 ∧
        ∀ s ∈ T.map (MulAut.conj (SemidirectProduct.inl y₀ : GamL Tag.D4 K)).toMonoidHom,
          conjAct Tag.D4 K s v = v) : False := by
  have hw1' : (w₁ : ModGL Tag.D4 K) ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨hQP, -⟩ := parabolic_root_radical_Levi_factors Tag.D4 K J
  set y : GamL Tag.D4 K := SemidirectProduct.inl y₀ with hy
  have hconjy : ∀ g : ModGL Tag.D4 K, conjAct Tag.D4 K y g = y₀ * g * y₀⁻¹ := fun g => by
    rw [hy, conjAct_inl, MulAut.conj_apply]
  have hconjyinv : ∀ g : ModGL Tag.D4 K, conjAct Tag.D4 K y⁻¹ g = y₀⁻¹ * g * y₀ := fun g => by
    rw [map_inv, hy, conjAct_inl, ← map_inv, MulAut.conj_apply, inv_inv]
  have hu : (w₁ : ModGL Tag.D4 K) ∈ parabolicRadical Tag.D4 K J := Subgroup.mem_subgroupOf.1 hwQ
  have hy₀P : y₀ ∈ parabolicSubgroup Tag.D4 K J := hQP hy₀
  have hu' : y₀ * (w₁ : ModGL Tag.D4 K) * y₀⁻¹ ∈ parabolicRadical Tag.D4 K J :=
    (Subgroup.mem_normalizer_iff.1 (parabolicSubgroup_le_normalizer_parabolicRadical J hy₀P) _).1 hu
  have hu'1 : y₀ * (w₁ : ModGL Tag.D4 K) * y₀⁻¹ ≠ 1 := fun h => hw1' (by
    have := congrArg (fun z => y₀⁻¹ * z * y₀) h
    simpa [mul_assoc] using this)
  have hfixT : ∀ s ∈ T, conjAct Tag.D4 K s (w₁ : ModGL Tag.D4 K) = w₁ := by
    intro s hs
    obtain ⟨α, hα, hαs⟩ := hT2 s hs
    rw [← hαs, hwC α hα]
  have hfix : ∀ s ∈ T.map (MulAut.conj y).toMonoidHom,
      conjAct Tag.D4 K s (y₀ * (w₁ : ModGL Tag.D4 K) * y₀⁻¹) =
        y₀ * (w₁ : ModGL Tag.D4 K) * y₀⁻¹ := by
    rintro _ ⟨s, hs, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have h1 : conjAct Tag.D4 K y⁻¹ (y₀ * (w₁ : ModGL Tag.D4 K) * y₀⁻¹) = w₁ := by
      rw [hconjyinv]; group
    rw [conjAct_conj, h1, hfixT s hs, hconjy]
  obtain ⟨v, hvQ, hv1, hvfix⟩ := hdual _ hu' hu'1 hfix
  have hvG : v ∈ adjointGroup Tag.D4 K := rootSpan_le_adjointGroup K _ hvQ
  have hy₀G : y₀ ∈ adjointGroup Tag.D4 K := rootSpan_le_adjointGroup K _ hy₀
  have hwG : y₀⁻¹ * v * y₀ ∈ adjointGroup Tag.D4 K :=
    mul_mem (mul_mem (inv_mem hy₀G) hvG) hy₀G
  have hwfix : ∀ s ∈ T, conjAct Tag.D4 K s (y₀⁻¹ * v * y₀) = y₀⁻¹ * v * y₀ := by
    intro s hs
    have h := hvfix _ (Subgroup.mem_map_of_mem _ hs)
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h
    rw [conjAct_conj, hconjyinv, hconjy] at h
    calc conjAct Tag.D4 K s (y₀⁻¹ * v * y₀) =
        y₀⁻¹ * (y₀ * conjAct Tag.D4 K s (y₀⁻¹ * v * y₀) * y₀⁻¹) * y₀ := by group
      _ = y₀⁻¹ * v * y₀ := by rw [h]
  have hwC' : (⟨y₀⁻¹ * v * y₀, hwG⟩ : ↥(adjointGroup Tag.D4 K)) ∈ autCentralizer R := by
    intro α hα
    refine Subtype.ext ?_
    obtain ⟨s, hs, hαs⟩ := hT1 α hα
    rw [hαs]
    exact hwfix s hs
  have hwP : y₀⁻¹ * v * y₀ ∈ parabolicSubgroup Tag.D4 K J := Subgroup.mem_subgroupOf.1 (hC hwC')
  have hvP : v ∈ parabolicSubgroup Tag.D4 K J := by
    have e : v = y₀ * (y₀⁻¹ * v * y₀) * y₀⁻¹ := by group
    rw [e]
    exact mul_mem (mul_mem hy₀P hwP) (inv_mem hy₀P)
  have h0 := Subgroup.mem_inf.2 ⟨hvP, hvQ⟩
  rw [parabolicSubgroup_inf_oppRadical] at h0
  exact hv1 (Subgroup.mem_bot.1 h0)


theorem autCentralizer_inf_radG_eq_bot_D4 (J : Set (Fin Tag.D4.rank)) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) {R : Subgroup (MulAut ↥(adjointGroup Tag.D4 K))} (hR : IsPGroup p R)
    (hQR : ∀ α ∈ R, (radG Tag.D4 K J).map α.toMonoidHom = radG Tag.D4 K J)
    (hNQ : Subgroup.normalizer ((radG Tag.D4 K J : Subgroup ↥(adjointGroup Tag.D4 K)) :
      Set ↥(adjointGroup Tag.D4 K)) = parG Tag.D4 K J)
    (hC : autCentralizer R ≤ parG Tag.D4 K J) :
    autCentralizer R ⊓ radG Tag.D4 K J = ⊥ := by
  classical
  have hfinM : Finite (ModGL Tag.D4 K) := finite_modGL
  have : Fact p.Prime := ⟨hp⟩
  have hchar : ringChar K = 2 := ringChar.eq K 2
  by_contra hne
  obtain ⟨⟨w₁, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  obtain ⟨hwC, hwQ⟩ := Subgroup.mem_inf.1 hw
  have hw1' : w₁ ≠ 1 := fun h => hw1 (Subtype.ext h)
  obtain ⟨T, hTL, hTodd, hT1, hT2⟩ := exists_lift_group hchar hp hp2 hR
  have hTodd' : ¬ 2 ∣ Nat.card T := by
    intro h
    obtain ⟨k, hk⟩ := hTodd
    omega
  have hshape : ∀ s ∈ T, ∃ (g : adjointGroup Tag.D4 K) (i : ℕ), g ∈ parG Tag.D4 K J ∧
      s.left = (g : ModGL Tag.D4 K) * d4P K ^ i ∧
        (i % 3 ≠ 0 → ∀ j, d4Rho j ∈ J ↔ j ∈ J) := by
    intro s hs
    obtain ⟨g', hg', i, hgi⟩ := (mem_sup_zpowers_d4P_iff d4P_mem_normalizer_adjointGroup).1
      (show s.left ∈ adjointGroup Tag.D4 K ⊔ Subgroup.zpowers (d4P K) from hTL hs)
    obtain ⟨α, hα, hαs⟩ := hT2 s hs
    set g : adjointGroup Tag.D4 K := ⟨g', hg'⟩ with hgdef
    have hsm : s = d4MkLift g s.right i := SemidirectProduct.ext hgi rfl
    have hαeq : α = MulAut.conj g * (exactNormalAut Tag.D4 K 1 s.right 0 * d4Graph K i) := by
      rw [← d4LiftHom_mkLift_eq]
      refine MulEquiv.ext fun h => Subtype.ext ?_
      rw [hαs h, coe_d4LiftHom_d4MkLift, conjAct_apply, hgi]
      rfl
    have hAmem : exactNormalAut Tag.D4 K 1 s.right 0 * d4Graph K i ∈ unipotentPairAut Tag.D4 K :=
      mul_mem (exactNormalAut_mem _ _ _) (d4Graph_mem i)
    have hg : g ∈ parG Tag.D4 K J := mem_parG_of_unipotentPair hAmem hαeq (hQR α hα) hNQ
    refine ⟨g, i, hg, hgi, fun hi => ?_⟩
    exact d4_stable_of_pow hi (d4_stable_of_normalizes hαeq hg (hQR α hα) hNQ)
  by_cases hJ : ∀ j, d4Rho j ∈ J ↔ j ∈ J
  ·
    have hTP : ∀ s ∈ T, s.left ∈ parabolicSubgroup Tag.D4 K J ⊔ Subgroup.zpowers (d4P K) := by
      intro s hs
      obtain ⟨g, i, hg, hsl, -⟩ := hshape s hs
      rw [hsl]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.1 hg))
        (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) i))
    obtain ⟨y₀, hy₀, hyM⟩ := exists_conj_into_levi_P J hJ hTP hTodd'
    refine d4_core_tail hT1 hT2 hC hwC hwQ hw1' hy₀ ?_
    intro u hu hu1 hfix
    have hSform : ∀ s ∈ T.map (MulAut.conj (SemidirectProduct.inl y₀ : GamL Tag.D4 K)).toMonoidHom,
        ∃ m ∈ parabolicLevi Tag.D4 K J, ∃ i : ℕ, s.left = m * d4P K ^ i := by
      rintro _ ⟨s, hs, rfl⟩
      obtain ⟨m, hm, i, hmi⟩ := (mem_sup_zpowers_d4P_iff (d4P_mem_normalizer_levi hJ)).1
        (hyM s hs)
      exact ⟨m, hm, i, hmi⟩
    have hSodd : Odd (Nat.card (T.map (MulAut.conj (SemidirectProduct.inl y₀ :
        GamL Tag.D4 K)).toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
      exact hTodd
    exact exists_fixed_mem_oppRadical_tri hJ hSform hSodd hu hu1 hfix
  ·
    have hTP : ∀ s ∈ T, s.left ∈ parabolicSubgroup Tag.D4 K J := by
      intro s hs
      obtain ⟨g, i, hg, hsl, hst⟩ := hshape s hs
      have hi : i % 3 = 0 := by
        by_contra hi
        exact hJ (hst hi)
      rw [hsl, d4P_pow_eq_one_of_mod hi, mul_one]
      exact Subgroup.mem_subgroupOf.1 hg
    obtain ⟨y₀, hy₀, hyM⟩ := exists_conj_into_levi J hTP hTodd'
    refine d4_core_tail hT1 hT2 hC hwC hwQ hw1' hy₀ ?_
    intro u hu hu1 hfix
    have hSM : ∀ s ∈ T.map (MulAut.conj (SemidirectProduct.inl y₀ : GamL Tag.D4 K)).toMonoidHom,
        s.left ∈ parabolicLevi Tag.D4 K J := by
      rintro _ ⟨s, hs, rfl⟩
      exact hyM s hs
    have hSodd : Odd (Nat.card (T.map (MulAut.conj (SemidirectProduct.inl y₀ :
        GamL Tag.D4 K)).toMonoidHom)) := by
      rw [Subgroup.card_map_of_injective (MulAut.conj _).injective]
      exact hTodd
    exact exists_fixed_mem_oppRadical_semi (Or.inl rfl) hSM hSodd hu hu1 hfix

end Cert

end CFSG.LieType.ChevTwo.Semi
