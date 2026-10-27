module

public import CFSG.HardMathSupport.Malle.SeitzCube.E6PlaneTwisted
public import CFSG.HardMathSupport.Malle.SeitzCube.PlanesE78
public import CFSG.LieType.Chevalley.EvenCartanRootDiagonals
public import CFSG.LieType.Chevalley.LangRootArithmeticDet
public import Certificates.Kernel.ThCent.Leaves

public noncomputable section

namespace CFSG.HardMathSupport.Malle.SeitzCube

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.TauCetiBridge CFSG.HardMathSupport.Malle.Proving
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section Transport

variable {G H : Type*} [Group G] [Group H] {p r : ℕ}

theorem PlaneNormalizing.map {E R : Subgroup G} (h : PlaneNormalizing p r E R) (φ : G →* H)
    (hφ : Function.Injective φ) : PlaneNormalizing p r (E.map φ) (R.map φ) := by
  obtain ⟨⟨hEc, hEp⟩, hc, hR, hRp, hN⟩ := h
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, ?_⟩, ?_, ?_, hRp.map φ, ?_⟩
  · obtain ⟨_, ⟨x, hx, rfl⟩⟩ := a
    obtain ⟨_, ⟨y, hy, rfl⟩⟩ := b
    refine Subtype.ext ?_
    change φ x * φ y = φ y * φ x
    rw [← map_mul, ← map_mul]
    exact congrArg φ (congrArg Subtype.val (hEc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩))
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hEp x hx, map_one]
  · rw [Subgroup.card_map_of_injective hφ, hc]
  · rwa [Ne, Subgroup.map_eq_bot_iff_of_injective _ hφ]
  · rintro _ ⟨x, hx, rfl⟩
    have key : ((MulAut.conj (φ x)).toMonoidHom).comp φ = φ.comp (MulAut.conj x).toMonoidHom :=
      MonoidHom.ext fun y => by simp [MulAut.conj_apply]
    rw [Subgroup.map_map, key, ← Subgroup.map_map, hN x hx]

theorem PlaneNormalizing.comap {E R : Subgroup G} (h : PlaneNormalizing p r E R) (φ : H →* G)
    (hφ : Function.Injective φ) (hE : E ≤ φ.range) (hR : R ≤ φ.range) :
    PlaneNormalizing p r (E.comap φ) (R.comap φ) := by
  obtain ⟨⟨hEc, hEp⟩, hc, hR0, hRp, hN⟩ := h
  have hmapE : (E.comap φ).map φ = E := Subgroup.map_comap_eq_self hE
  have hmapR : (R.comap φ).map φ = R := Subgroup.map_comap_eq_self hR
  refine ⟨⟨⟨⟨fun a b => Subtype.ext (hφ ?_)⟩⟩, fun x hx => hφ ?_⟩, ?_, ?_, ?_, fun x hx => ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (hEc.is_comm.comm (⟨φ a, a.2⟩ : E) ⟨φ b, b.2⟩)
  · rw [map_pow, map_one]
    exact hEp _ hx
  · rw [← hc]
    conv_rhs => rw [← hmapE]
    exact (Subgroup.card_map_of_injective hφ).symm
  · intro hbot
    refine hR0 ?_
    rw [← hmapR, hbot, Subgroup.map_bot]
  · exact hRp.comap_of_injective φ hφ
  · refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      change φ (x * y * x⁻¹) ∈ R
      rw [map_mul, map_mul, map_inv, ← hN (φ x) hx]
      exact ⟨φ y, hy, rfl⟩
    · intro y hy
      have hy' : φ y ∈ R.map (MulAut.conj (φ x)).toMonoidHom := by rw [hN (φ x) hx]; exact hy
      obtain ⟨z, hz, hzy⟩ := hy'
      obtain ⟨z', rfl⟩ := hR hz
      refine ⟨z', hz, hφ ?_⟩
      change φ (x * z' * x⁻¹) = φ y
      rw [map_mul, map_mul, map_inv]
      exact hzy

end Transport

section E6


theorem rootDiagUnit_cube_mem_E6 {K : Type} [Field K] (b : Fin Tag.E6.rank → Kˣ) :
    rootDiagUnit Tag.E6 (fun i => b i ^ 3) ∈ adjointGroup Tag.E6 K := by
  have hdet : Tag.E6.cartan.transpose.det = 3 := by
    rw [Matrix.det_transpose]
    exact det_cartan_E6
  have hle : torusGroup Tag.E6 K ≤ adjointGroup Tag.E6 K :=
    (Subgroup.closure_le _).2 fun _ ⟨q, hq⟩ => hq ▸ torusElt_mem_adjointGroup q.1 q.2
  rw [rootDiagUnit_eq_list_prod_torusElt_adjugate (u := b) fun i => by
    rw [hdet]
    exact zpow_natCast (b i) 3]
  exact hle (list_prod_torusElt_mem_torusGroup _)

theorem mem_map_baseChange_of_frobenius_fixed_E6 {K L : Type} [Field K] [Finite K] [Field L]
    [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {x : ModGL .E6 L} (hx : x ∈ adjointGroup .E6 L) (hxF : Units.map (entrywiseHom Fr) x = x)
    (hcop : ringChar K ≠ 3 → Nat.Coprime 3 (orderOf x)) :
    x ∈ (adjointGroup .E6 K).map (baseChangeGL (algebraMap K L)) := by
  classical
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  set H := (adjointGroup Tag.E6 K).map (baseChangeGL (algebraMap K L)) with hH
  obtain ⟨a, u, hu, rfl⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed .E6 Fr hFr hx hxF
  by_cases h3 : ringChar K = 3
  ·
    have : Fact (ringChar K).Prime := ⟨by rw [h3]; exact Nat.prime_three⟩
    have : CharP K 3 := h3 ▸ ringChar.charP K
    have hcube : ∀ i, ∃ b : Kˣ, b ^ 3 = a i := fun i => by
      obtain ⟨c, hc⟩ := surjective_frobenius K 3 (a i : K)
      have hc0 : c ≠ 0 := fun h0 => (a i).ne_zero (by rw [← hc, h0, frobenius_def, zero_pow three_ne_zero])
      exact ⟨Units.mk0 c hc0, Units.ext (by simpa [frobenius_def] using hc)⟩
    choose b hb using hcube
    have hab : a = fun i => b i ^ 3 := funext fun i => (hb i).symm
    rw [hab]
    exact mul_mem (Subgroup.mem_map_of_mem _ (rootDiagUnit_cube_mem_E6 b)) hu
  ·
    set t := baseChangeGL (algebraMap K L) (rootDiagUnit Tag.E6 a) with ht
    have hconj : ∀ b : Fin Tag.E6.rank → Kˣ, ∀ h ∈ H,
        baseChangeGL (algebraMap K L) (rootDiagUnit Tag.E6 b) * h *
          (baseChangeGL (algebraMap K L) (rootDiagUnit Tag.E6 b))⁻¹ ∈ H := by
      rintro b _ ⟨h₀, hh₀, rfl⟩
      refine ⟨rootDiagUnit Tag.E6 b * h₀ * (rootDiagUnit Tag.E6 b)⁻¹,
        conj_rootDiagUnit_mem_adjointGroup b hh₀, ?_⟩
      rw [map_mul, map_mul, map_inv]
    have htN : ∀ h ∈ H, t⁻¹ * h * t ∈ H := fun h hh => by
      have e : t⁻¹ = baseChangeGL (algebraMap K L) (rootDiagUnit Tag.E6 a⁻¹) := by
        rw [ht, ← map_inv, rootDiagUnit_inv]
      have := hconj a⁻¹ h hh
      rwa [← e, inv_inv] at this
    have ht3 : t ^ 3 ∈ H := by
      refine ⟨rootDiagUnit Tag.E6 (fun i => a i ^ 3), rootDiagUnit_cube_mem_E6 a, ?_⟩
      rw [ht, ← map_pow]
      congr 1
      have e : (fun i => a i ^ 3) = a * a * a := funext fun i => by
        simp only [Pi.mul_apply]
        exact pow_three' (a i)
      rw [e, rootDiagUnit_mul, rootDiagUnit_mul, pow_three']
    have hx3 : (t * u) ^ 3 ∈ H := by
      have e : (t * u) ^ 3 = t ^ 3 * (t⁻¹ * (t⁻¹ * u * t) * t) * (t⁻¹ * u * t) * u := by
        simp only [pow_three', mul_assoc, mul_inv_cancel_left]
      rw [e]
      have h1 : t⁻¹ * u * t ∈ H := htN u hu
      exact mul_mem (mul_mem (mul_mem ht3 (htN _ h1)) h1) hu
    obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (hcop h3)
    rw [← hm]
    exact pow_mem hx3 m

end E6

section Cat


theorem conj_injective_cat_E6 (q : TauCeti.PrimePower) (hv : (TauCeti.LieTypeIndex.E6 q).Valid) :
    Function.Injective (MulAut.conj : Cat ⟨TauCeti.LieTypeIndex.E6 q, hv⟩ →*
      MulAut (Cat ⟨TauCeti.LieTypeIndex.E6 q, hv⟩)) := by
  obtain ⟨K, _, _, -, -, ⟨e⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  exact conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot)

theorem exists_plane_cat_E6_of_twisted (q : TauCeti.PrimePower)
    (hv : (TauCeti.LieTypeIndex.E6 q).Valid) {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3)
    (h : ∀ (K : Type) [Field K] [Finite K], Nat.card K = q.card → CharP K q.p →
      ∀ (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L),
        (∀ c, Fr c = c ^ q.card) → ∃ n ∈ adjointGroup Tag.E6 L, ∃ E R : Subgroup (ModGL Tag.E6 L),
          E ≤ twistFix Tag.E6 Fr n ∧ R ≤ twistFix Tag.E6 Fr n ∧ PlaneNormalizing p q.p E R) :
    ∃ E : Subgroup (MulAut (Cat ⟨TauCeti.LieTypeIndex.E6 q, hv⟩)), IsElemAbelian p E ∧
      Nat.card E = p ^ 2 ∧ InnerPlane ⟨TauCeti.LieTypeIndex.E6 q, hv⟩ p E ∧
        NormalizesRSubgroup ⟨TauCeti.LieTypeIndex.E6 q, hv⟩ E := by
  classical
  obtain ⟨K, _, _, hK, hKc, ⟨ε⟩⟩ := exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.e6 q hv
  have : Fact q.p.Prime := ⟨q.prime_p⟩
  let L := AlgebraicClosure K
  have : CharP L q.p := charP_of_injective_algebraMap (algebraMap K L).injective q.p
  let Fr : L →+* L := iterateFrobenius L q.p q.exponent
  have hFr : ∀ c, Fr c = c ^ q.card := fun c => by
    rw [TauCeti.PrimePower.card_def q]
    exact iterateFrobenius_def q.p q.exponent c
  have hFrK : ∀ c, Fr c = c ^ Nat.card K := fun c => by rw [hFr, hK]
  obtain ⟨n, hn, E, R, hET, hRT, hER⟩ := h K hK hKc L Fr hFr
  obtain ⟨g0, hg0C, hg0⟩ := CFSG.RankThree.PartOne.KE.lang_conjugator_gen .E6 K
    (ℓ := q.p) (f := q.exponent) q.exponent_pos L n hn
  have hg0' : Units.map (entrywiseHom Fr) g0 = g0 * n := hg0
  let ι : ↥(adjointGroup .E6 K) →* ModGL .E6 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .E6 K).subtype
  have hι : Function.Injective ι := (baseChangeGL_injective _).comp Subtype.val_injective
  have hrange : ι.range = (adjointGroup .E6 K).map (baseChangeGL (algebraMap K L)) := by
    change ((baseChangeGL (algebraMap K L)).comp (adjointGroup .E6 K).subtype).range = _
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let c : ModGL .E6 L →* ModGL .E6 L := (MulAut.conj g0).toMonoidHom
  have hc : Function.Injective c := (MulAut.conj g0).injective
  have hchar : ringChar K = q.p := ringChar.eq K q.p
  have hland : ∀ x ∈ twistFix .E6 Fr n, (ringChar K ≠ 3 → Nat.Coprime 3 (orderOf x)) →
      c x ∈ ι.range := by
    intro x hx hcop
    obtain ⟨hxC, hxF⟩ := hx
    have hxF' : n * Units.map (entrywiseHom Fr) x * n⁻¹ = x := hxF
    have hF : Units.map (entrywiseHom Fr) (g0 * x * g0⁻¹) = g0 * x * g0⁻¹ := by
      rw [map_mul, map_mul, map_inv, hg0']
      calc g0 * n * Units.map (entrywiseHom Fr) x * (g0 * n)⁻¹
          = g0 * (n * Units.map (entrywiseHom Fr) x * n⁻¹) * g0⁻¹ := by group
        _ = g0 * x * g0⁻¹ := by rw [hxF']
    rw [hrange]
    refine mem_map_baseChange_of_frobenius_fixed_E6 Fr hFrK
      (mul_mem (mul_mem hg0C hxC) (inv_mem hg0C)) hF fun h3 => ?_
    have : orderOf (c x) = orderOf x := MulEquiv.orderOf_eq (MulAut.conj g0) x
    rw [this]
    exact hcop h3
  have hE : E.map c ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    refine hland x (hET hx) fun _ => ?_
    have hdvd : orderOf x ∣ p := orderOf_dvd_of_pow_eq_one (hER.1.2 x hx)
    rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
    · rw [h1]; exact Nat.coprime_one_right 3
    · rw [h1]; exact (Nat.coprime_primes Nat.prime_three hp).2 (Ne.symm hp3)
  have hR : R.map c ≤ ι.range := by
    rintro _ ⟨x, hx, rfl⟩
    refine hland x (hRT hx) fun h3 => ?_
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.1 hER.2.2.2.1 ⟨x, hx⟩
    have hxo : orderOf x = q.p ^ k := by
      rw [← hk]
      exact (orderOf_submonoid (H := R.toSubmonoid) ⟨x, hx⟩)
    rw [hxo]
    refine Nat.Coprime.pow_right _ ((Nat.coprime_primes Nat.prime_three q.prime_p).2 ?_)
    rw [← hchar]
    exact Ne.symm h3
  have hφ : Function.Injective (ε.symm.toMonoidHom) := ε.symm.injective
  obtain ⟨hE', hc', hR0, hRp, hN⟩ := ((hER.map c hc).comap ι hι hE hR).map _ hφ
  have hinj := conj_injective_cat_E6 q hv
  have hn' : ((E.map c).comap ι).map ε.symm.toMonoidHom ≤
      Subgroup.normalizer ((((R.map c).comap ι).map ε.symm.toMonoidHom : Subgroup _) : Set _) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    have hx' := hN x hx
    constructor
    · intro hy
      rw [← hx']
      exact ⟨y, hy, rfl⟩
    · intro hy
      rw [← hx'] at hy
      obtain ⟨z, hz, hzy⟩ := hy
      have : z = y := by
        have h := congrArg (fun t => x⁻¹ * t * x) hzy
        simpa [MulAut.conj_apply, mul_assoc] using h
      rwa [← this]
  obtain ⟨A, hA, hAc, hAin, hAN⟩ := exists_plane_of_subgroup hinj hE' hc' hn'
  refine ⟨A, hA, hAc, hAin, _, hR0, ?_, hAN⟩
  rw [TauCeti.LieTypeIndex.characteristic_E6]
  exact hRp

theorem excPlaneE6E3_proved : ExcPlaneE6E3 := by
  rintro ⟨d, hv⟩ p hp hp2 hpd hex ⟨q, rfl, hnd, hdvd⟩ hr
  have hp3 := ne_three_of_dvd_sq_add_add_one hnd hdvd
  refine exists_plane_cat_E6_of_twisted q hv hp hp3 fun K _ _ hK hKc L _ _ _ Fr hFr => ?_
  have hT := twistedPlaneE6_three K L Fr (fun c => by rw [hFr, hK]) p hp ⟨hp3, by rwa [hK]⟩
  rwa [ringChar.eq K q.p] at hT

end Cat

end CFSG.HardMathSupport.Malle.SeitzCube
