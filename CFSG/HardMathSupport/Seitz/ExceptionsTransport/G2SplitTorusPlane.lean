module

public import CFSG.LieType.SeitzGeneration.RegimesExc
public import CFSG.LieType.SeitzGeneration.ExcPlaneModel
public import CFSG.LieType.SeitzGeneration.ExcPlaneBridge
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.G2Rows
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

namespace CFSG.HardMathSupport.Seitz.ExceptionsTransport

theorem padicValNat_ordG2_of_dvd_sub_one {q p : ℕ} (hq : 2 ≤ q) (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ q - 1) : padicValNat p (CFSG.Open.ordG2 q) = 2 * padicValNat p (q - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  have hpm : p ∣ m := by simpa using hpq
  have hm0 : m ≠ 0 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have h6 : (m + 1) ^ 6 - 1 = m * (m ^ 5 + 6 * m ^ 4 + 15 * m ^ 3 + 20 * m ^ 2 + 15 * m + 6) := by
    have : (m + 1) ^ 6 = m * (m ^ 5 + 6 * m ^ 4 + 15 * m ^ 3 + 20 * m ^ 2 + 15 * m + 6) + 1 := by
      ring
    rw [this, Nat.add_sub_cancel]
  have h2 : (m + 1) ^ 2 - 1 = m * (m + 2) := by
    have : (m + 1) ^ 2 = m * (m + 2) + 1 := by ring
    rw [this, Nat.add_sub_cancel]
  have hP : ¬ p ∣ (m ^ 5 + 6 * m ^ 4 + 15 * m ^ 3 + 20 * m ^ 2 + 15 * m + 6) := by
    intro h
    have hA : p ∣ m ^ 5 + 6 * m ^ 4 + 15 * m ^ 3 + 20 * m ^ 2 + 15 * m := by
      refine dvd_add (dvd_add (dvd_add (dvd_add ?_ ?_) ?_) ?_) ?_
      · exact dvd_pow hpm (by norm_num)
      · exact (dvd_pow hpm (by norm_num)).mul_left 6
      · exact (dvd_pow hpm (by norm_num)).mul_left 15
      · exact (dvd_pow hpm (by norm_num)).mul_left 20
      · exact hpm.mul_left 15
    have h' : p ∣ 6 := (Nat.dvd_add_right hA).1 h
    have h6le := Nat.le_of_dvd (by norm_num) h'
    interval_cases p
    · omega
    · exact absurd hp (by norm_num)
  have hm2 : ¬ p ∣ m + 2 := by
    intro h
    have : p ∣ 2 := (Nat.dvd_add_right hpm).1 h
    have := Nat.le_of_dvd (by norm_num) this
    omega
  have hm1 : ¬ p ∣ m + 1 := by
    intro h
    have : p ∣ 1 := (Nat.dvd_add_right hpm).1 h
    exact hp.one_lt.ne' (Nat.dvd_one.1 this)
  have hP0 : (m ^ 5 + 6 * m ^ 4 + 15 * m ^ 3 + 20 * m ^ 2 + 15 * m + 6) ≠ 0 := by positivity
  have hpow : padicValNat p ((m + 1) ^ 6) = 0 := by
    rw [padicValNat.pow (m + 1) 6, padicValNat.eq_zero_of_not_dvd hm1]
  unfold CFSG.Open.ordG2
  rw [h6, h2]
  rw [padicValNat.mul (by positivity) (by positivity), padicValNat.mul (by positivity) (by positivity),
    padicValNat.mul hm0 hP0, padicValNat.mul hm0 (by omega), hpow,
    padicValNat.eq_zero_of_not_dvd hP, padicValNat.eq_zero_of_not_dvd hm2]
  simp only [Nat.add_sub_cancel]
  ring

section Sylow

variable
  {K : Type} [Field K] [Finite K]

theorem exists_conj_le_torus {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K - 1)
    (F : Subgroup (adjointGroup .G2 K)) (hF : IsPGroup p F) :
    ∃ g : adjointGroup .G2 K, ∀ x ∈ F, ∃ y ∈ torusGroup .G2 K, (x : ModGL .G2 K) = g * y * g⁻¹ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hTA : torusGroup .G2 K ≤ adjointGroup .G2 K := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨⟨i, s⟩, rfl⟩
    exact torusElt_mem_adjointGroup i s
  set T : Subgroup (adjointGroup .G2 K) := (torusGroup .G2 K).subgroupOf (adjointGroup .G2 K)
    with hT
  have hTcard : Nat.card T = (Nat.card K - 1) ^ 2 := by
    rw [hT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTA).toEquiv]
    exact CFSG.Timmesfeld.ExceptionalOrders.card_torusGroup_G2
  have hq : 2 ≤ Nat.card K := Finite.one_lt_card
  have hAcard := CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2 (K := K)
  have hv : (Nat.card (adjointGroup .G2 K)).factorization p = (Nat.card T).factorization p := by
    rw [Nat.factorization_def _ hp, Nat.factorization_def _ hp, hAcard, hTcard,
      padicValNat_ordG2_of_dvd_sub_one hq hp hp5 hpq, padicValNat.pow (Nat.card K - 1) 2]
  obtain ⟨P⟩ := (Sylow.nonempty (G := T) (p := p))
  have hPcard : Nat.card (P.map T.subtype) = p ^ (Nat.card (adjointGroup .G2 K)).factorization p := by
    rw [Subgroup.card_map_of_injective T.subtype_injective, P.card_eq_multiplicity, hv]
  let S : Sylow p (adjointGroup .G2 K) := Sylow.ofCard (P.map T.subtype) hPcard
  obtain ⟨Q, hFQ⟩ := hF.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (adjointGroup .G2 K) S Q
  refine ⟨g, fun x hx => ?_⟩
  have hxQ : x ∈ Q := hFQ hx
  rw [← hg, ← SetLike.mem_coe, Sylow.coe_smul] at hxQ
  obtain ⟨w, hw, hwx⟩ := hxQ
  have hw' : w ∈ (P.map T.subtype : Subgroup (adjointGroup .G2 K)) := hw
  obtain ⟨u, hu, rfl⟩ := hw'
  refine ⟨((u : T) : adjointGroup .G2 K).1, ?_, ?_⟩
  · exact Subgroup.mem_subgroupOf.1 u.2
  · have : x = g * (T.subtype u) * g⁻¹ := by
      rw [← hwx]; rfl
    rw [this]; rfl

end Sylow

section CatLevel

open CFSG.LieType.SeitzGeneration CFSG.Open TauCeti

theorem map_conj_comap_eq {C G : Type*} [Group C] [Group G] (ι : C →* G) (M : Subgroup G) (c : C)
    (hc : ι c ∈ Subgroup.normalizer (M : Set G)) :
    (M.comap ι).map (MulAut.conj c).toMonoidHom = M.comap ι := by
  have hc' : (ι c)⁻¹ ∈ Subgroup.normalizer (M : Set G) := Subgroup.inv_mem _ hc
  ext x
  constructor
  · rintro ⟨r, hr, rfl⟩
    have h := (Subgroup.mem_normalizer_iff.1 hc (ι r)).1 hr
    simpa [map_mul, map_inv] using h
  · intro hx
    refine ⟨c⁻¹ * x * c, ?_, ?_⟩
    · have h := (Subgroup.mem_normalizer_iff.1 hc' (ι x)).1 hx
      simpa [map_mul, map_inv] using h
    · show c * (c⁻¹ * x * c) * c⁻¹ = x
      group

end CatLevel

section CatLevel2

open CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport CFSG.LieType.SeitzGeneration CFSG.Open CFSG.AGLEmbeddingD2 CFSG.TauCetiBridge TauCeti


theorem pinnedX_pow_nat {K : Type} [Field K] {τ : Tag} (α : Fin τ.rank → ℤ) (c : K) (n : ℕ) :
    pinnedX τ K α c ^ n = pinnedX τ K α (n * c) := by
  induction n with
  | zero => simp [pinnedX_zero]
  | succ n ih => rw [pow_succ, ih, ← pinnedX_add]; congr 1; push_cast; ring

theorem g2_innerPlane_normalizesR_of_dvd_sub_one (q : PrimePower)
    (hv : (LieTypeIndex.G2 q).Valid) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ q.card - 1)
    (E : Subgroup (MulAut (Cat ⟨.G2 q, hv⟩))) (hE : IsElemAbelian p E)
    (hin : E ≤ (MulAut.conj : Cat ⟨.G2 q, hv⟩ →* MulAut (Cat ⟨.G2 q, hv⟩)).range) :
    NormalizesRSubgroup ⟨.G2 q, hv⟩ E := by
  obtain ⟨K, _, _, hK, hKchar, ⟨e⟩⟩ :=
    exists_catEquiv_adjointGroup Even.chevalleyBridgesAll.g2 q hv
  have hinj : Function.Injective (MulAut.conj : Cat ⟨.G2 q, hv⟩ →* MulAut (Cat ⟨.G2 q, hv⟩)) :=
    conj_injective_of_mulEquiv e (conj_injective_of_center_eq_bot center_adjointGroup_eq_bot)
  let ι : Cat ⟨.G2 q, hv⟩ →* ModGL .G2 K := (adjointGroup .G2 K).subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  let FC : Subgroup (Cat ⟨.G2 q, hv⟩) := E.comap (MulAut.conj : Cat ⟨.G2 q, hv⟩ →* _)
  let FA : Subgroup (adjointGroup .G2 K) := FC.map e.toMonoidHom
  have hFA : IsPGroup p FA := by
    intro x
    obtain ⟨c, hc, hcx⟩ := x.2
    refine ⟨1, Subtype.ext ?_⟩
    have h1 : (MulAut.conj c) ^ p = 1 := hE.2 _ hc
    have h2 : c ^ p = 1 := hinj (by rw [map_pow, h1, map_one])
    show (x : adjointGroup .G2 K) ^ p ^ 1 = 1
    rw [pow_one, ← hcx]
    show e c ^ p = 1
    rw [← map_pow, h2, map_one]
  obtain ⟨g, hg⟩ := exists_conj_le_torus (K := K) hp hp5 (by rw [hK]; exact hpq) FA hFA
  set U := rootSubgroup .G2 K gA with hU
  set M : Subgroup (ModGL .G2 K) := U.comap (MulAut.conj (g : ModGL .G2 K)⁻¹).toMonoidHom with hM
  refine ⟨M.comap ι, ?_, ?_, ?_⟩
  · intro h
    have hgA : (g : ModGL .G2 K) ∈ adjointGroup .G2 K := g.2
    have hX : pinnedX .G2 K gA 1 ∈ adjointGroup .G2 K := pinnedX_mem_adjointGroup _ _
    have hmemA : (g : ModGL .G2 K) * pinnedX .G2 K gA 1 * (g : ModGL .G2 K)⁻¹ ∈
        adjointGroup .G2 K := Subgroup.mul_mem _ (Subgroup.mul_mem _ hgA hX) (Subgroup.inv_mem _ hgA)
    set c0 : Cat ⟨.G2 q, hv⟩ := e.symm ⟨_, hmemA⟩ with hc0
    have hιc0 : ι c0 = (g : ModGL .G2 K) * pinnedX .G2 K gA 1 * (g : ModGL .G2 K)⁻¹ := by
      simp [ι, hc0]
    have hmem : c0 ∈ M.comap ι := by
      show ι c0 ∈ M
      rw [hιc0]
      show (MulAut.conj (g : ModGL .G2 K)⁻¹) _ ∈ U
      have : (MulAut.conj (g : ModGL .G2 K)⁻¹) ((g : ModGL .G2 K) * pinnedX .G2 K gA 1 *
          (g : ModGL .G2 K)⁻¹) = pinnedX .G2 K gA 1 := by
        simp; group
      rw [this]
      exact Subgroup.subset_closure ⟨1, rfl⟩
    rw [h, Subgroup.mem_bot] at hmem
    rw [hmem, map_one] at hιc0
    have h1 : pinnedX .G2 K gA 1 = 1 := by
      have := congrArg (fun x => (g : ModGL .G2 K)⁻¹ * x * g) hιc0
      simpa [mul_assoc] using this.symm
    exact one_ne_zero (pinnedX_injective .G2 K gA (h1.trans (pinnedX_zero .G2 K gA).symm))
  · intro x
    have hchar : (⟨LieTypeIndex.G2 q, hv⟩ : ValidLieTypeIndex).1.characteristic = q.p := by
      simp
    refine ⟨1, ?_⟩
    rw [hchar]
    refine Subtype.ext ?_
    have hx : ι x ∈ M := x.2
    have hx' : (g : ModGL .G2 K)⁻¹ * ι x * (g : ModGL .G2 K) ∈ U := by
      have := hx
      simpa [hM, MulAut.conj_apply] using this
    obtain ⟨t, ht⟩ := mem_rootSubgroup.1 hx'
    have hιx : ι x = (g : ModGL .G2 K) * pinnedX .G2 K gA t * (g : ModGL .G2 K)⁻¹ := by
      rw [ht]; group
    have hrp : (ι x) ^ q.p = 1 := by
      rw [hιx, conj_pow, pinnedX_pow_nat, CharP.cast_eq_zero K q.p, zero_mul,
        pinnedX_zero .G2 K gA]
      group
    have h1 : ((x : Cat ⟨.G2 q, hv⟩)) ^ q.p = 1 := hι (by rw [map_pow, hrp]; exact (map_one ι).symm)
    show ((x ^ q.p ^ 1 : ↥(M.comap ι)) : Cat ⟨.G2 q, hv⟩) = 1
    rw [pow_one]
    exact h1
  · intro ε hε
    obtain ⟨c, rfl⟩ := hin hε
    have hcFC : c ∈ FC := hε
    obtain ⟨y, hy, hyc⟩ := hg (e c) ⟨c, hcFC, rfl⟩
    have hynorm := torusGroup_le_normalizer_rootSubgroup (R := K) (τ := .G2) isRoot_gA hy
    refine map_conj_comap_eq ι M c ?_
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hιc : ι c = (g : ModGL .G2 K) * y * (g : ModGL .G2 K)⁻¹ := hyc
    have key : ∀ h : ModGL .G2 K, h ∈ M ↔
        ι c * h * (ι c)⁻¹ ∈ M := by
      intro h
      have e1 : (g : ModGL .G2 K)⁻¹ * (ι c * h * (ι c)⁻¹) * (g : ModGL .G2 K) =
          y * ((g : ModGL .G2 K)⁻¹ * h * (g : ModGL .G2 K)) * y⁻¹ := by
        rw [hιc]; group
      have hmem : ∀ z : ModGL .G2 K, z ∈ M ↔ (g : ModGL .G2 K)⁻¹ * z * (g : ModGL .G2 K) ∈ U := by
        intro z; simp [hM]
      rw [hmem, hmem, e1]
      exact Subgroup.mem_normalizer_iff.1 hynorm _
    exact key h

end CatLevel2

end CFSG.HardMathSupport.Seitz.ExceptionsTransport
