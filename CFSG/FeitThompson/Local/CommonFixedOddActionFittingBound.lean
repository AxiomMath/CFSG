module

public import CFSG.FeitThompson.Local.CommonFixedActionPQuotientFitting
public import CFSG.FeitThompson.Local.FittingFixedFreeDisplacementInFitting
public import CFSG.FeitThompson.Local.ChiefFactorCentralizationFittingBound
public import CFSG.FeitThompson.Local.InvariantRankTwoFactorsFixedFreeCycle
public import CFSG.FeitThompson.Local.CentralSylowFixedFreeCycle
public import CFSG.FeitThompson.Foundations.CoprimeAutomorphismFaithfulFitting
public import CFSG.FeitThompson.Foundations.OrderDescentProperSubgroup

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG.FeitThompson

open Subgroup QuotientGroup

variable {G : Type*} [Group G]

theorem subgroupOf_inf_centralizer {L X Y : Subgroup G} (hYL : Y ≤ L) :
    (X ⊓ centralizer (Y : Set G)).subgroupOf L
      = X.subgroupOf L ⊓ centralizer ((Y.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  refine and_congr_right fun _ => ?_
  simp only [Subgroup.mem_centralizer_iff]
  constructor
  · intro hc y hy
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hy
    exact Subtype.ext (hc _ hy)
  · intro hc y hy
    exact congrArg Subtype.val
      (hc ⟨y, hYL hy⟩ (by rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]; exact hy))

theorem subgroupOf_inf_centralizer_singleton {L : Subgroup G} (X : Subgroup G) (y : ↥L) :
    (X ⊓ centralizer ({(y : G)} : Set G)).subgroupOf L
      = X.subgroupOf L ⊓ centralizer ({y} : Set ↥L) := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  refine and_congr_right fun _ => ?_
  simp only [Subgroup.mem_centralizer_singleton_iff]
  exact ⟨fun hc => Subtype.ext hc, fun hc => congrArg Subtype.val hc⟩

theorem subgroupOf_fittingOfNormal_of_le [Finite G] {K L : Subgroup G} (hKL : K ≤ L) :
    (fittingOfNormal K).subgroupOf L = fittingOfNormal (K.subgroupOf L) := by
  rw [← map_subtype_fittingOfNormal_subgroupOf hKL]
  exact Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

theorem commutator_le_fittingOfNormal_of_le_normalizer [Finite G] [Group.IsSolvable G]
    (hodd : Odd (Nat.card G)) {K R : Subgroup G} (hRK : R ≤ normalizer (K : Set G))
    (hdisj : Disjoint K R) (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R))
    {p a : ℕ} (hp : p.Prime) (hKF : (fittingOfNormal K).relIndex K = p ^ a)
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ centralizer ({x} : Set G) = K ⊓ centralizer (R : Set G))
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥) :
    ⁅K, R⁆ ≤ fittingOfNormal K := by
  set L : Subgroup G := K ⊔ R
  have hKL : K ≤ L := le_sup_left
  have hRL : R ≤ L := le_sup_right
  have hLnorm : L ≤ normalizer (K : Set G) := sup_le le_normalizer hRK
  have hKn : (K.subgroupOf L).Normal := normal_subgroupOf_of_le_normalizer hKL hLnorm
  have hcompl : (K.subgroupOf L).IsComplement' (R.subgroupOf L) :=
    isComplement'_subgroupOf_sup hRK hdisj
  have hcardK : Nat.card ↥(K.subgroupOf L) = Nat.card ↥K :=
    Nat.card_congr (subgroupOfEquivOfLe hKL).toEquiv
  have hcardR : Nat.card ↥(R.subgroupOf L) = Nat.card ↥R :=
    Nat.card_congr (subgroupOfEquivOfLe hRL).toEquiv
  have hcop' : (Nat.card ↥(K.subgroupOf L)).Coprime (Nat.card ↥(R.subgroupOf L)) := by
    rw [hcardK, hcardR]; exact hcop
  have hC' : ∀ x ∈ R.subgroupOf L, x ≠ 1 →
      K.subgroupOf L ⊓ centralizer ({x} : Set ↥L)
        = K.subgroupOf L ⊓ centralizer ((R.subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    intro x hx hx1
    rw [Subgroup.mem_subgroupOf] at hx
    rw [← subgroupOf_inf_centralizer_singleton, ← subgroupOf_inf_centralizer hRL,
      hC (x : G) hx (fun h => hx1 (Subtype.ext h))]
  have hcent' : fittingOfNormal (K.subgroupOf L)
      ⊓ centralizer ((R.subgroupOf L : Subgroup ↥L) : Set ↥L) = ⊥ := by
    rw [← subgroupOf_fittingOfNormal_of_le hKL, ← subgroupOf_inf_centralizer hRL, hcent,
      Subgroup.bot_subgroupOf]
  have key := commutator_le_fittingOfNormal_of_forall_inf_centralizer_eq
    (odd_natCard_subgroup hodd L) hcompl hcop' hp
    (by rwa [relIndex_fittingOfNormal_subgroupOf hKL]) hC' hcent'
  have := Subgroup.map_mono (f := L.subtype) key
  rwa [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype, Subgroup.subgroupOf_map_subtype,
    inf_eq_left.2 hKL, inf_eq_left.2 hRL, map_subtype_fittingOfNormal_subgroupOf hKL] at this

theorem le_normalizer_fittingOfNormal (K : Subgroup G) [Finite G] :
    normalizer (K : Set G) ≤ normalizer ((fittingOfNormal K : Subgroup G) : Set G) := by
  rw [← map_fittingRaw_subtype_eq_fittingOfNormal]
  exact normalizer_le_normalizer_map_subtype K (fittingRaw ↥K)

theorem normal_fittingOfNormal_subgroupOf [Finite G] {K P : Subgroup G} (hPK : P ≤ K)
    (hFP : fittingOfNormal K ≤ P) : ((fittingOfNormal K).subgroupOf P).Normal :=
  normal_subgroupOf_of_le_normalizer hFP
    (hPK.trans ((le_normalizer (H := K)).trans (le_normalizer_fittingOfNormal K)))

theorem fittingOfNormal_eq_of_le [Finite G] {P K : Subgroup G} (hPK : P ≤ K)
    (hP : (P.subgroupOf K).Normal) (hFP : fittingOfNormal K ≤ P) :
    fittingOfNormal P = fittingOfNormal K := by
  refine le_antisymm ?_ ?_
  · calc fittingOfNormal P = (fittingOfNormal (P.subgroupOf K)).map K.subtype :=
          (map_subtype_fittingOfNormal_subgroupOf hPK).symm
      _ = ((fittingRaw ↥(P.subgroupOf K)).map (P.subgroupOf K).subtype).map K.subtype := by
          rw [map_fittingRaw_subtype_eq_fittingOfNormal]
      _ ≤ (fittingRaw ↥K).map K.subtype :=
          Subgroup.map_mono (map_subtype_fittingRaw_le_fittingRaw hP)
      _ = fittingOfNormal K := map_fittingRaw_subtype_eq_fittingOfNormal K
  · have hnil : Group.IsNilpotent ↥(fittingOfNormal K) := by
      rw [← map_fittingRaw_subtype_eq_fittingOfNormal]
      exact isNilpotent_map_subtype_fittingRaw K
    have := le_map_fittingRaw_subtype hFP (normal_fittingOfNormal_subgroupOf hPK hFP) hnil
    rwa [map_fittingRaw_subtype_eq_fittingOfNormal] at this

def fittingQuotientConj [Finite G] {K R : Subgroup G} (hRK : R ≤ normalizer (K : Set G)) :
    ↥R →* MulAut (↥K ⧸ fittingRaw ↥K) :=
  (isInvariantSubgroup_of_characteristic (conjOnNormalized K hRK) (fittingRaw ↥K)).quotientAut

@[simp]
theorem fittingQuotientConj_mk [Finite G] {K R : Subgroup G} (hRK : R ≤ normalizer (K : Set G))
    (r : ↥R) (k : ↥K) :
    fittingQuotientConj hRK r (QuotientGroup.mk k)
      = QuotientGroup.mk (conjOnNormalized K hRK r k) :=
  IsInvariantSubgroup.quotientAut_mk _ r k

theorem mem_fittingRaw_iff_coe_mem_fittingOfNormal [Finite G] (K : Subgroup G) (x : ↥K) :
    x ∈ fittingRaw ↥K ↔ (x : G) ∈ fittingOfNormal K := by
  rw [← subgroupOf_fittingOfNormal K, Subgroup.mem_subgroupOf]

theorem commutator_le_fittingOfNormal_of_fittingQuotientConj_eq_one [Finite G] {K R : Subgroup G}
    (hRK : R ≤ normalizer (K : Set G)) (h : ∀ r : ↥R, fittingQuotientConj hRK r = 1) :
    ⁅K, R⁆ ≤ fittingOfNormal K := by
  refine Subgroup.commutator_le.2 fun k hk r hr => ?_
  set x : ↥K := ⟨k⁻¹, K.inv_mem hk⟩ with hx
  have hfix : (QuotientGroup.mk x : ↥K ⧸ fittingRaw ↥K)
      = QuotientGroup.mk (conjOnNormalized K hRK ⟨r, hr⟩ x) := by
    rw [← fittingQuotientConj_mk hRK ⟨r, hr⟩ x, h ⟨r, hr⟩, MulAut.one_apply]
  rw [QuotientGroup.eq] at hfix
  have hco : ((x⁻¹ * conjOnNormalized K hRK ⟨r, hr⟩ x : ↥K) : G) = k * r * k⁻¹ * r⁻¹ := by
    rw [Subgroup.coe_mul, InvMemClass.coe_inv, conjOnNormalized_apply_coe, hx]
    group
  rw [commutatorElement_def, ← hco]
  exact (mem_fittingRaw_iff_coe_mem_fittingOfNormal K _).1 hfix

theorem fittingQuotientConj_apply_mk_eq_self [Finite G] {K R S : Subgroup G}
    (hRK : R ≤ normalizer (K : Set G)) (h : ⁅S, R⁆ ≤ fittingOfNormal K) (r : ↥R) {k : ↥K}
    (hk : (k : G) ∈ S) :
    fittingQuotientConj hRK r (QuotientGroup.mk k) = QuotientGroup.mk k := by
  rw [fittingQuotientConj_mk, QuotientGroup.eq]
  have hmem : ((r : G) * (k : G)⁻¹ * (r : G)⁻¹ * (k : G)) ∈ ⁅S, R⁆ := by
    rw [Subgroup.commutator_comm]
    simpa [commutatorElement_def] using
      Subgroup.commutator_mem_commutator (H₁ := R) (H₂ := S) r.2 (S.inv_mem hk)
  have hco : (((conjOnNormalized K hRK r k)⁻¹ * k : ↥K) : G)
      = (r : G) * (k : G)⁻¹ * (r : G)⁻¹ * (k : G) := by
    rw [Subgroup.coe_mul, InvMemClass.coe_inv, conjOnNormalized_apply_coe]
    group
  exact (mem_fittingRaw_iff_coe_mem_fittingOfNormal K _).2 (hco ▸ h hmem)

theorem natCard_lt_of_lt [Finite G] {H K : Subgroup G} (h : H < K) :
    Nat.card ↥H < Nat.card ↥K := by
  have := Set.Finite.card_lt_card (s := (H : Set G)) (t := (K : Set G)) (Set.toFinite _)
    (by exact_mod_cast h)
  simpa using this

theorem commutator_le_fittingOfNormal_of_le_normalizer_of_natCard_le [Finite G]
    [Group.IsSolvable G] (hodd : Odd (Nat.card G)) (n : ℕ) :
    ∀ K R : Subgroup G, Nat.card ↥K ≤ n → R ≤ normalizer (K : Set G) → Disjoint K R →
      (Nat.card ↥K).Coprime (Nat.card ↥R) →
      (∀ x ∈ R, x ≠ 1 → K ⊓ centralizer ({x} : Set G) = K ⊓ centralizer (R : Set G)) →
      fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥ →
      ⁅K, R⁆ ≤ fittingOfNormal K := by
  induction n with
  | zero =>
    intro K R hcard _ _ _ _ _
    have : 0 < Nat.card ↥K := Nat.card_pos
    omega
  | succ n ih =>
    intro K R hcard hRK hdisj hcop hC hcent
    set N : Subgroup ↥K := fittingRaw ↥K with hN
    have key : ∀ p : ℕ, p.Prime →
        ⁅(Subgroup.comap (mk' N) (pCore p (↥K ⧸ N))).map K.subtype, R⁆ ≤ fittingOfNormal K := by
      intro p hp
      set P' : Subgroup ↥K := Subgroup.comap (mk' N) (pCore p (↥K ⧸ N)) with hP'
      have : P'.Characteristic :=
        Subgroup.Characteristic.comap_quotient_mk (pCore_characteristic _ _)
      set P : Subgroup G := P'.map K.subtype with hP
      have hPK : P ≤ K := Subgroup.map_subtype_le _
      have hPsub : P.subgroupOf K = P' :=
        Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
      have hPnormal : (P.subgroupOf K).Normal := by rw [hPsub]; infer_instance
      have hNP' : N ≤ P' := by
        intro y hy
        rw [hP', Subgroup.mem_comap, QuotientGroup.mk'_apply,
          (QuotientGroup.eq_one_iff y).2 hy]
        exact one_mem _
      have hFP : fittingOfNormal K ≤ P := by
        rw [← map_fittingRaw_subtype_eq_fittingOfNormal, hP]
        exact Subgroup.map_mono hNP'
      have hFPeq : fittingOfNormal P = fittingOfNormal K :=
        fittingOfNormal_eq_of_le hPK hPnormal hFP
      have hRP : R ≤ normalizer (P : Set G) :=
        hRK.trans (normalizer_le_normalizer_map_subtype K P')
      have hdisjP : Disjoint P R := hdisj.mono_left hPK
      have hcopP : (Nat.card ↥P).Coprime (Nat.card ↥R) :=
        hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hPK)
      have hCP : ∀ x ∈ R, x ≠ 1 →
          P ⊓ centralizer ({x} : Set G) = P ⊓ centralizer (R : Set G) := by
        intro x hx hx1
        rw [← inf_eq_left.2 hPK, inf_assoc, hC x hx hx1, ← inf_assoc, inf_eq_left.2 hPK]
      have hcentP : fittingOfNormal P ⊓ centralizer (R : Set G) = ⊥ := by rw [hFPeq]; exact hcent
      rcases eq_or_lt_of_le hPK with heq | hlt
      ·
        have hPtop : P' = ⊤ := by rw [← hPsub, heq, Subgroup.subgroupOf_self]
        have hQtop : pCore p (↥K ⧸ N) = ⊤ := by
          have h0 := Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective N) (pCore p (↥K ⧸ N))
          rw [← h0, ← hP', hPtop, Subgroup.map_top_of_surjective _
            (QuotientGroup.mk'_surjective N)]
        have : Fact p.Prime := ⟨hp⟩
        have hpg : IsPGroup p (↥K ⧸ N) := by
          have h1 := isPGroup_pCore hp (↥K ⧸ N)
          rw [hQtop] at h1
          exact h1.of_equiv Subgroup.topEquiv
        obtain ⟨a, ha⟩ := hpg.exists_card_eq
        rw [heq]
        exact commutator_le_fittingOfNormal_of_le_normalizer hodd hRK hdisj hcop hp
          (by rw [relIndex_fittingOfNormal, ← hN, ha]) hC hcent
      ·
        have hlt' : Nat.card ↥P ≤ n :=
          Nat.lt_succ_iff.1 (lt_of_lt_of_le (natCard_lt_of_lt hlt) hcard)
        have := ih P R hlt' hRP hdisjP hcopP hCP hcentP
        rwa [hFPeq] at this
    set ρ : ↥R →* MulAut (↥K ⧸ N) := fittingQuotientConj hRK
    have hfix : ∀ r : ↥R, ∀ x ∈ fittingRaw (↥K ⧸ N), ρ r x = x := by
      intro r
      have hsub : fittingRaw (↥K ⧸ N)
          ≤ MonoidHom.eqLocus (ρ r : (↥K ⧸ N) →* (↥K ⧸ N)) (MonoidHom.id _) := by
        rw [fittingRaw_eq_iSup_pCore]
        refine iSup₂_le fun p hp => fun x hx => ?_
        obtain ⟨k, hk⟩ := QuotientGroup.mk_surjective (s := N) x
        have hkP : (k : G) ∈ (Subgroup.comap (mk' N) (pCore p (↥K ⧸ N))).map K.subtype := by
          refine Subgroup.mem_map.2 ⟨k, ?_, rfl⟩
          rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, hk]
          exact hx
        have h2 := fittingQuotientConj_apply_mk_eq_self hRK (key p hp) r hkP
        rw [hk] at h2
        exact h2
      exact fun x hx => hsub hx
    refine commutator_le_fittingOfNormal_of_fittingQuotientConj_eq_one hRK fun r => ?_
    set A : Subgroup (MulAut (↥K ⧸ N)) := ρ.range
    have hcopA : (Nat.card ↥A).Coprime (Nat.card (↥K ⧸ N)) := by
      refine Nat.Coprime.coprime_dvd_left (Subgroup.card_range_dvd ρ) ?_
      exact hcop.symm.coprime_dvd_right (Subgroup.card_quotient_dvd_card N)
    have := eq_one_of_fixes_fittingRaw A.subtype A.subtype_injective hcopA
      (a := ⟨ρ r, ⟨r, rfl⟩⟩) (fun x hx => hfix r x hx)
    exact congrArg Subtype.val this

theorem commutator_le_fittingOfNormal_of_forall_inf_centralizer_eq_of_coprime [Finite G]
    [Group.IsSolvable G] (hodd : Odd (Nat.card G)) {K R : Subgroup G} [K.Normal]
    (hKR : K.IsComplement' R) (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R))
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ centralizer ({x} : Set G) = K ⊓ centralizer (R : Set G))
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥) :
    ⁅K, R⁆ ≤ fittingOfNormal K :=
  commutator_le_fittingOfNormal_of_le_normalizer_of_natCard_le hodd (Nat.card ↥K) K R le_rfl
    le_normalizer_of_normal hKR.disjoint hcop hC hcent

theorem subgroupOf_commutator_le_fittingRaw_of_forall_inf_centralizer_eq_of_coprime [Finite G]
    [Group.IsSolvable G] (hodd : Odd (Nat.card G)) {K R : Subgroup G} [K.Normal]
    (hKR : K.IsComplement' R) (hcop : (Nat.card ↥K).Coprime (Nat.card ↥R))
    (hC : ∀ x ∈ R, x ≠ 1 → K ⊓ centralizer ({x} : Set G) = K ⊓ centralizer (R : Set G))
    (hcent : fittingOfNormal K ⊓ centralizer (R : Set G) = ⊥) :
    (⁅K, R⁆ : Subgroup G).subgroupOf K ≤ fittingRaw ↥K :=
  (le_map_fittingRaw_subtype_iff (Subgroup.commutator_le_left K R)).1
    (map_fittingRaw_subtype_eq_fittingOfNormal K ▸
      commutator_le_fittingOfNormal_of_forall_inf_centralizer_eq_of_coprime hodd hKR hcop hC hcent)

end CFSG.FeitThompson
