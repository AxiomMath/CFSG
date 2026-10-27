module

import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64FreeCenter
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGLHyp111Config
public import CFSG.LocalAnalysis.SectionRank.AmbientRank

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen

open CFSG.Open CFSG.LocalAnalysis.RankThreeTheoremC.Hyp111
open CFSG.RankThreeCoreUniqueness.Helpers Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

theorem exists_mul_ne_of_sq_dvd_card {G : Type*} [Group G] [IsSimpleGroup G] {p : ℕ}
    (hp : p.Prime) (h : p ^ 2 ∣ Nat.card G) (hG : Nat.card G ≠ 0) :
    ∃ a b : G, a * b ≠ b * a := by
  by_contra hc
  push Not at hc
  letI : CommGroup G := { ‹Group G› with mul_comm := hc }
  have hq : (Nat.card G).Prime := IsSimpleGroup.prime_card
  rcases (Nat.dvd_prime hq).mp h with h1 | h1
  · exact hp.one_lt.ne' (Nat.pow_eq_one.mp h1 |>.resolve_right (by norm_num))
  · have hpq : p ∣ Nat.card G := (dvd_pow_self p two_ne_zero).trans h
    rcases (Nat.dvd_prime hq).mp hpq with h2 | h2
    · exact hp.one_lt.ne' h2
    · rw [← h2, sq] at h1
      exact hp.one_lt.ne' (Nat.eq_of_mul_eq_mul_left hp.pos (h1.trans (mul_one p).symm))

section Transport

variable {p : ℕ} [Fact p.Prime] {Y : Type} [Group Y] [Finite Y] {K Y₀ : Subgroup Y} [K.Normal]

omit [Fact p.Prime] [Finite Y] [K.Normal] in
private theorem subgroupOf_ne_top (hKY₀ : ¬ K ≤ Y₀) : Y₀.subgroupOf K ≠ ⊤ := fun htop =>
  hKY₀ fun k hk => mem_subgroupOf.mp (htop ▸ mem_top (⟨k, hk⟩ : K))

theorem isSolvable_inf_of_forall_sylow_le (R : Sylow p Y)
    (hK : ∀ (T : Sylow p K) (H : Subgroup K), (T : Subgroup K) ≤ H → H ≠ ⊤ →
      Group.IsSolvable H)
    (hRY₀ : (R : Subgroup Y) ≤ Y₀) (hKY₀ : ¬ K ≤ Y₀) :
    Group.IsSolvable (K ⊓ Y₀ : Subgroup Y) := by
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have hTH : (T : Subgroup K) ≤ Y₀.subgroupOf K := fun t ht => by
    have h : (t : Y) ∈ (R : Subgroup Y) ⊓ K := hT ▸ mem_map_of_mem K.subtype ht
    exact mem_subgroupOf.mpr (hRY₀ h.1)
  haveI := hK T _ hTH (subgroupOf_ne_top hKY₀)
  let f : (K ⊓ Y₀ : Subgroup Y) →* Y₀.subgroupOf K :=
    { toFun := fun x => ⟨⟨x, x.2.1⟩, mem_subgroupOf.mpr x.2.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := f) fun x y h =>
    Subtype.ext (congrArg (fun z : Y₀.subgroupOf K => ((z : K) : Y)) h)

theorem exists_pCore_inf_of_forall_normalizer_le (R : Sylow p Y)
    (hK : ∀ (T : Sylow p K) (H : Subgroup K), normalizer ((T : Subgroup K) : Set K) ≤ H →
      H ≠ ⊤ → ∃ N : Subgroup K, N ≤ H ∧ IsPGroup p N ∧ H ≤ normalizer (N : Set K) ∧
        centralizer (N : Set K) ⊓ H ≤ N)
    (hN : normalizer (((R : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ⊓ K ≤ Y₀)
    (hKY₀ : ¬ K ≤ Y₀) :
    ∃ N : Subgroup Y, N ≤ K ⊓ Y₀ ∧ IsPGroup p N ∧ K ⊓ Y₀ ≤ normalizer (N : Set Y) ∧
      centralizer (N : Set Y) ⊓ (K ⊓ Y₀) ≤ N := by
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  have hTH : normalizer ((T : Subgroup K) : Set K) ≤ Y₀.subgroupOf K := fun k hk => by
    refine mem_subgroupOf.mpr (hN ⟨?_, k.2⟩)
    have h := le_normalizer_map K.subtype (mem_map_of_mem K.subtype hk)
    rwa [hT] at h
  obtain ⟨N, hNH, hNp, hHN, hCN⟩ := hK T _ hTH (subgroupOf_ne_top hKY₀)
  refine ⟨N.map K.subtype, ?_, hNp.map _, fun y hy => ?_, ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    exact ⟨n.2, mem_subgroupOf.mp (hNH hn)⟩
  · have hy' : (⟨y, hy.1⟩ : K) ∈ normalizer (N : Set K) := hHN (mem_subgroupOf.mpr hy.2)
    exact le_normalizer_map K.subtype (mem_map_of_mem K.subtype hy')
  · rintro y ⟨hyC, hyK, hyY₀⟩
    have hy' : (⟨y, hyK⟩ : K) ∈ centralizer (N : Set K) ⊓ Y₀.subgroupOf K := by
      refine ⟨mem_centralizer_iff.mpr fun n hn => Subtype.ext ?_, mem_subgroupOf.mpr hyY₀⟩
      exact mem_centralizer_iff.mp hyC n (mem_map_of_mem K.subtype hn)
    exact mem_map_of_mem K.subtype (hCN hy')

theorem exists_pCore_of_normalizer_le_of_mulEquiv {L M : Type*} [Group L] [Group M] [Finite L]
    (e : L ≃* M)
    (hM : ∀ (T : Sylow p M) (H : Subgroup M), normalizer ((T : Subgroup M) : Set M) ≤ H →
      H ≠ ⊤ → ∃ N : Subgroup M, N ≤ H ∧ IsPGroup p N ∧ H ≤ normalizer (N : Set M) ∧
        centralizer (N : Set M) ⊓ H ≤ N)
    (T : Sylow p L) (H : Subgroup L) (hTH : normalizer ((T : Subgroup L) : Set L) ≤ H)
    (hH : H ≠ ⊤) :
    ∃ N : Subgroup L, N ≤ H ∧ IsPGroup p N ∧ H ≤ normalizer (N : Set L) ∧
      centralizer (N : Set L) ⊓ H ≤ N := by
  obtain ⟨N, hNH, hNp, hHN, hCN⟩ := hM (T.mapSurjective e.surjective) (H.map e.toMonoidHom)
    (by
      rw [Sylow.coe_mapSurjective, ← map_equiv_normalizer_eq]
      exact map_mono hTH)
    (fun htop => hH (by
      rw [← comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective H, htop, comap_top]))
  refine ⟨N.map e.symm.toMonoidHom, ?_, hNp.map _, fun h hh => ?_, fun x hx => ?_⟩
  · rintro _ ⟨n, hn, rfl⟩
    obtain ⟨h, hh, rfl⟩ := hNH hn
    simpa using hh
  · have h1 : e h ∈ normalizer (N : Set M) := hHN (mem_map_of_mem _ hh)
    rw [← map_equiv_normalizer_eq]
    exact ⟨e h, h1, by simp⟩
  · obtain ⟨hxC, hxH⟩ := mem_inf.mp hx
    have h1 : e x ∈ centralizer (N : Set M) ⊓ H.map e.toMonoidHom := by
      refine mem_inf.mpr ⟨mem_centralizer_iff.mpr fun n hn => ?_, mem_map_of_mem _ hxH⟩
      have h2 := mem_centralizer_iff.mp hxC (e.symm n) (mem_map_of_mem _ hn)
      simpa using congrArg e h2
    exact ⟨e x, hCN h1, by simp⟩

end Transport

section Core

variable {p : ℕ} {Y : Type} [Group Y] [Finite Y]

theorem normalizer_le_of_three_le_pRank_of_le (hp : p.Prime) {Y₀ E X : Subgroup Y}
    (R : Sylow p Y)
    (hcore : (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
      else GLBCore p 1 E) ≤ Y₀)
    (hXR : X ≤ R) (hX : 3 ≤ CFSG.Open.pRank p X) : normalizer (X : Set Y) ≤ Y₀ := by
  have hR : 3 ≤ pRank p (R : Subgroup Y) := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hX.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp hXR)
  rw [if_pos hR] at hcore
  exact (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p hXR (by omega)
    (hX.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp le_sup_left))).trans hcore

variable [Fact p.Prime] {K : Subgroup Y} [K.Normal]

theorem exists_inv_mul_mem_centralizer_of_not_dvd (hout : ¬ p ∣ Nat.card (Outer K)) {r : Y}
    {n : ℕ} (hr : r ^ p ^ n = 1) : ∃ k ∈ K, k⁻¹ * r ∈ centralizer (K : Set Y) := by
  set o : Outer K := QuotientGroup.mk (MulAut.conjNormal r : MulAut K) with ho
  have hop : o ^ p ^ n = 1 := by
    rw [ho, ← QuotientGroup.mk_pow, ← map_pow, hr, map_one, QuotientGroup.mk_one]
  have h1 : orderOf o = 1 := by
    obtain ⟨i, -, hio⟩ := (Nat.dvd_prime_pow Fact.out).1 (orderOf_dvd_of_pow_eq_one hop)
    rcases i with _ | i
    · simpa using hio
    · exact absurd ((dvd_pow_self p i.succ_ne_zero).trans (hio ▸ orderOf_dvd_natCard o)) hout
  rw [orderOf_eq_one_iff, ho, QuotientGroup.eq_one_iff] at h1
  obtain ⟨k, hk⟩ := h1
  refine ⟨k, k.2, mem_centralizer_iff.mpr fun m hm => ?_⟩
  have h := congrArg Subtype.val (DFunLike.congr_fun hk ⟨m, hm⟩)
  simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h
  calc m * ((k : Y)⁻¹ * r) = (k : Y)⁻¹ * ((k : Y) * m * (k : Y)⁻¹) * r := by group
    _ = (k : Y)⁻¹ * (r * m * r⁻¹) * r := by rw [h]
    _ = (k : Y)⁻¹ * r * m := by group

private theorem mem_inf_of_mem_normalizer (R : Sylow p Y) {k : Y} (hkK : k ∈ K) {n : ℕ}
    (hkn : k ^ p ^ n = 1)
    (hkN : k ∈ normalizer (((R : Subgroup Y) ⊓ K : Subgroup Y) : Set Y)) :
    k ∈ (R : Subgroup Y) ⊓ K := by
  obtain ⟨T, hT⟩ := CFSG.QuasithinUnique.exists_sylow_map_eq_inf_of_normal R K
  set T₀ : Subgroup Y := (R : Subgroup Y) ⊓ K
  have hkp : IsPGroup p (zpowers k) := by
    rintro ⟨g, hg⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hg
    refine ⟨n, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hkn, one_zpow]
  have hT₀p : IsPGroup p T₀ := hT ▸ T.isPGroup'.map K.subtype
  have hH : IsPGroup p (zpowers k ⊔ T₀ : Subgroup Y) :=
    IsPGroup.to_sup_of_normal_right' hkp hT₀p (zpowers_le.mpr hkN)
  have hHK : (zpowers k ⊔ T₀ : Subgroup Y) ≤ K := sup_le (zpowers_le.mpr hkK) inf_le_right
  have hle : (T : Subgroup K) ≤ (zpowers k ⊔ T₀ : Subgroup Y).subgroupOf K := fun t ht =>
    mem_subgroupOf.mpr (mem_sup_right (hT ▸ mem_map_of_mem K.subtype ht))
  have hHp : IsPGroup p ((zpowers k ⊔ T₀ : Subgroup Y).subgroupOf K) :=
    hH.comap_of_injective K.subtype K.subtype_injective
  have heq := T.is_maximal' hHp hle
  have hk : (⟨k, hkK⟩ : K) ∈ (zpowers k ⊔ T₀ : Subgroup Y).subgroupOf K :=
    mem_subgroupOf.mpr (mem_sup_left (mem_zpowers k))
  rw [heq] at hk
  rw [← hT]
  exact mem_map_of_mem K.subtype hk

theorem sylow_le_sup_inf_centralizer_of_not_dvd (R : Sylow p Y)
    (hZ : K ⊓ centralizer (K : Set Y) = ⊥) (hout : ¬ p ∣ Nat.card (Outer K)) :
    (R : Subgroup Y) ≤ ((R : Subgroup Y) ⊓ K) ⊔
      ((R : Subgroup Y) ⊓ centralizer (((R : Subgroup Y) ⊓ K : Subgroup Y) : Set Y)) := by
  intro r hr
  obtain ⟨n, hn⟩ := R.isPGroup' ⟨r, hr⟩
  have hrn : r ^ p ^ n = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨k, hkK, hc⟩ := exists_inv_mul_mem_centralizer_of_not_dvd hout hrn
  set c := k⁻¹ * r with hcdef
  have hrkc : r = k * c := by rw [hcdef, mul_inv_cancel_left]
  have hkc : Commute k c := mem_centralizer_iff.mp hc k hkK
  have hkn : k ^ p ^ n = 1 := by
    have h1 : (k * c) ^ p ^ n = k ^ p ^ n * c ^ p ^ n := hkc.mul_pow _
    rw [← hrkc, hrn] at h1
    have hmem : k ^ p ^ n ∈ K ⊓ centralizer (K : Set Y) := by
      refine mem_inf.mpr ⟨pow_mem hkK _, ?_⟩
      rw [eq_inv_of_mul_eq_one_left h1.symm]
      exact (centralizer (K : Set Y)).inv_mem ((centralizer (K : Set Y)).pow_mem hc _)
    rw [hZ] at hmem
    exact hmem
  have hcT : ∀ t ∈ K, c * t = t * c := fun t ht => (mem_centralizer_iff.mp hc t ht).symm
  have hconj : ∀ t ∈ K, k * t * k⁻¹ = r * t * r⁻¹ := fun t ht => by
    rw [hrkc]
    calc k * t * k⁻¹ = k * (t * c) * c⁻¹ * k⁻¹ := by group
      _ = k * (c * t) * c⁻¹ * k⁻¹ := by rw [hcT t ht]
      _ = k * c * t * (k * c)⁻¹ := by group
  have hkN : k ∈ normalizer (((R : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) := by
    rw [mem_normalizer_iff]
    intro t
    constructor
    · intro ht
      obtain ⟨htR, htK⟩ := mem_inf.mp ht
      rw [hconj t htK]
      exact mem_inf.mpr ⟨R.toSubgroup.mul_mem (R.toSubgroup.mul_mem hr htR)
        (R.toSubgroup.inv_mem hr), ‹K.Normal›.conj_mem t htK r⟩
    · intro ht
      obtain ⟨htR, htK⟩ := mem_inf.mp ht
      have htK' : t ∈ K := by
        have h := ‹K.Normal›.conj_mem _ htK k⁻¹
        rwa [show k⁻¹ * (k * t * k⁻¹) * k⁻¹⁻¹ = t by group] at h
      rw [hconj t htK'] at htR
      refine mem_inf.mpr ⟨?_, htK'⟩
      have h := R.toSubgroup.mul_mem (R.toSubgroup.mul_mem (R.toSubgroup.inv_mem hr) htR) hr
      rwa [show r⁻¹ * (r * t * r⁻¹) * r = t by group] at h
  have hkT := mem_inf_of_mem_normalizer R hkK hkn hkN
  have hcR : c ∈ (R : Subgroup Y) :=
    R.toSubgroup.mul_mem (R.toSubgroup.inv_mem (mem_inf.mp hkT).1) hr
  have hcC : c ∈ centralizer (((R : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) :=
    mem_centralizer_iff.mpr fun t ht => (hcT t (mem_inf.mp ht).2).symm
  rw [hrkc]
  exact mul_mem (mem_sup_left hkT) (mem_sup_right (mem_inf.mpr ⟨hcR, hcC⟩))

private theorem forall_mul_comm_of_card_eq (R : Sylow p Y) {Z : Subgroup Y}
    (hZR : Z ≤ R) (hZc : Nat.card Z = p) (hN : (R : Subgroup Y) ≤ normalizer (Z : Set Y)) :
    ∀ z ∈ Z, ∀ q ∈ (R : Subgroup Y), q * z = z * q := by
  haveI : Group.IsNilpotent (R : Subgroup Y) := R.isPGroup'.isNilpotent
  set Z' : Subgroup (R : Subgroup Y) := Z.subgroupOf R
  haveI : Z'.Normal := ⟨fun x hx g => mem_subgroupOf.mpr
    ((mem_normalizer_iff.mp (hN g.2) x).mp (mem_subgroupOf.mp hx))⟩
  have hZ'c : Nat.card Z' = p := (Nat.card_congr (subgroupOfEquivOfLe hZR).toEquiv).trans hZc
  have hne : Z' ≠ ⊥ := fun h => by
    rw [h, card_bot] at hZ'c
    exact (Fact.out : p.Prime).one_lt.ne hZ'c
  have hinf := Group.IsNilpotent.inf_center_ne_bot_of_normal hne
  have heq : Z' ⊓ center (R : Subgroup Y) = Z' := by
    have hdvd : Nat.card (Z' ⊓ center (R : Subgroup Y) : Subgroup (R : Subgroup Y)) ∣
        Nat.card Z' := card_dvd_of_le inf_le_left
    rw [hZ'c] at hdvd
    rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
    · exact absurd ((card_eq_one).mp h) hinf
    · exact eq_of_le_of_card_ge inf_le_left (by rw [h, hZ'c])
  intro z hz q hq
  have hz' : (⟨z, hZR hz⟩ : (R : Subgroup Y)) ∈ Z' := mem_subgroupOf.mpr hz
  rw [← heq] at hz'
  exact congrArg Subtype.val (mem_center_iff.mp (mem_inf.mp hz').2 ⟨q, hq⟩)

theorem normalizer_inf_le_of_card_center_eq {Y₀ E : Subgroup Y} (R : Sylow p Y)
    (hER : E ≤ R) (hE : IsElemAbelian p E) (hEc : Nat.card E = p ^ 2)
    (hcore : (if 3 ≤ pRank p (R : Subgroup Y) then GLBWeakCore p (R : Subgroup Y)
      else GLBCore p 1 E) ≤ Y₀)
    (hZ : K ⊓ centralizer (K : Set Y) = ⊥) (hout : ¬ p ∣ Nat.card (Outer K))
    (h2 : 2 ≤ CFSG.Open.pRank p ((R : Subgroup Y) ⊓ K))
    (hZT : Nat.card (center ((R : Subgroup Y) ⊓ K : Subgroup Y)) = p) :
    normalizer (((R : Subgroup Y) ⊓ K : Subgroup Y) : Set Y) ≤ Y₀ := by
  have hp : p.Prime := Fact.out
  set T₀ : Subgroup Y := (R : Subgroup Y) ⊓ K with hT₀
  by_cases h3 : 3 ≤ pRank p (R : Subgroup Y)
  · rw [if_pos h3] at hcore
    refine (CFSG.PreuniquenessRankFour.Helpers.normalizer_le_weakCore p inf_le_left h2
      ?_).trans hcore
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
    exact h3.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
      (sylow_le_sup_inf_centralizer_of_not_dvd R hZ hout))
  · rw [if_neg h3] at hcore
    have hR2 : CFSG.Open.pRank p (R : Subgroup Y) ≤ 2 := by
      rw [CFSG.SectionRank.pRank_coe_eq_openPRank] at h3
      omega
    set Z : Subgroup Y := (center T₀).map T₀.subtype with hZdef
    have hNZ : normalizer (T₀ : Set Y) ≤ normalizer (Z : Set Y) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (center T₀)
    have hZc : Nat.card Z = p := by
      rw [hZdef, card_map_of_injective T₀.subtype_injective, hZT]
    have hZT₀ : Z ≤ T₀ := map_subtype_le _
    have hZR : Z ≤ R := hZT₀.trans inf_le_left
    have hRN : (R : Subgroup Y) ≤ normalizer (T₀ : Set Y) := fun r hr => by
      rw [mem_normalizer_iff]
      intro t
      constructor
      · rintro ⟨htR, htK⟩
        exact ⟨R.toSubgroup.mul_mem (R.toSubgroup.mul_mem hr htR) (R.toSubgroup.inv_mem hr),
          ‹K.Normal›.conj_mem t htK r⟩
      · rintro ⟨htR, htK⟩
        have e : t = r⁻¹ * (r * t * r⁻¹) * r⁻¹⁻¹ := by group
        rw [e]
        exact ⟨R.toSubgroup.mul_mem (R.toSubgroup.mul_mem (R.toSubgroup.inv_mem hr) htR)
          (R.toSubgroup.inv_mem (R.toSubgroup.inv_mem hr)),
          ‹K.Normal›.conj_mem _ htK r⁻¹⟩
    have hcent := forall_mul_comm_of_card_eq R hZR hZc (hRN.trans hNZ)
    have hZE : Z ≤ E := fun z hz => by
      have hzp : z ^ p = 1 := by
        have h := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
        rw [hZc] at h
        simpa using congrArg Subtype.val h
      exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.P64Free.mem_of_central_of_pRank_le_two hp
        hR2 hER hE hEc (hZR hz) hzp fun q hq => hcent z hz q hq
    have hZel : IsElemAbelian p Z := by
      refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun z hz => ?_⟩
      · obtain ⟨x, hx, hxa⟩ := mem_map.mp a.2
        obtain ⟨y, hy, hyb⟩ := mem_map.mp b.2
        change (a : Y) * b = b * a
        rw [← hxa, ← hyb, ← map_mul, ← map_mul,
          (mem_center_iff.mp hy x : x * y = y * x).symm]
      · have h := pow_card_eq_one' (G := Z) (x := ⟨z, hz⟩)
        rw [hZc] at h
        simpa using congrArg Subtype.val h
    have hZr : 1 ≤ CFSG.Open.pRank p Z :=
      CFSG.SectionRank.le_pRank hp.one_lt le_rfl hZel (by rw [hZc, pow_one])
    exact hNZ.trans ((le_sSup ⟨Z, hZE, hZr, rfl⟩ : normalizer (Z : Set Y) ≤ GLBCore p 1 E).trans
      hcore)

end Core

end CFSG.LocalAnalysis.RankThreeTheoremC.TenThirteen
