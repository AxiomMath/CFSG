module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632Defs
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank632NearCyclic
import CFSG.LocalAnalysis.RankThreeTheoremC.GL83SmallRank627Lines
import CFSG.LocalAnalysis.PreuniquenessRankFour.CoprimeAction
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem stepBAction_not_three_dvd_card {H : Type*} [Group H] [Finite H]
    (hH : IsPGroup 2 H) : ¬ 3 ∣ Nat.card H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hH
  rw [hn]
  intro h
  have h2 := Nat.prime_three.dvd_of_dvd_pow h
  omega

omit [Finite G] in
private theorem stepBAction_commutator_le {T : Subgroup G} {z : G}
    (hz : z ∈ normalizer (T : Set G)) : ⁅T, zpowers z⁆ ≤ T :=
  le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hz)

omit [Finite G] in
private theorem stepBAction_le_normalizer {P T : Subgroup G} {z : G}
    (hPT : P ≤ normalizer (T : Set G)) (hz : z ∈ centralizer (P : Set G)) :
    P ≤ normalizer ((⁅T, zpowers z⁆ : Subgroup G) : Set G) := by
  intro p hp
  have hZ : p ∈ normalizer ((zpowers z : Subgroup G) : Set G) :=
    centralizer_le_normalizer _ (le_centralizer_iff.mp (zpowers_le.mpr hz) hp)
  rw [mem_normalizer_iff_map_conj_eq] at hZ ⊢
  rw [map_commutator, hZ, mem_normalizer_iff_map_conj_eq.mp (hPT hp)]

private theorem stepBAction_commutator_idem {T : Subgroup G} {z : G} (hT : IsPGroup 2 T)
    (hZ : IsPGroup 3 (zpowers z)) (hz : z ∈ normalizer (T : Set G)) :
    ⁅⁅T, zpowers z⁆, zpowers z⁆ = ⁅T, zpowers z⁆ :=
  CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3 Nat.prime_three
    (zpowers z) T hZ (stepBAction_not_three_dvd_card hT) (zpowers_le.mpr hz)

omit [Finite G] in
private theorem stepBAction_not_mem_centralizer {T : Subgroup G} {x z : G}
    (hidem : ⁅⁅T, zpowers z⁆, zpowers z⁆ = ⁅T, zpowers z⁆)
    (hnc : ¬ (T ⊓ centralizer ({x} : Set G)) ≤ centralizer ({z} : Set G)) :
    z ∉ centralizer ((⁅T, zpowers z⁆ : Subgroup G) : Set G) := by
  intro hz
  have h1 : ⁅⁅T, zpowers z⁆, zpowers z⁆ = ⊥ :=
    commutator_eq_bot_iff_le_centralizer.mpr (le_centralizer_iff.mp (zpowers_le.mpr hz))
  rw [hidem] at h1
  have h2 : T ≤ centralizer ((zpowers z : Subgroup G) : Set G) :=
    commutator_eq_bot_iff_le_centralizer.mp h1
  exact hnc (inf_le_left.trans
    (h2.trans (centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers z)))))

private theorem stepBAction_frattini_comm {R : Type*} [Group R] [Finite R] {p : ℕ}
    [Fact p.Prime] (hR : IsPGroup p R) (a b : R ⧸ frattini R) : a * b = b * a := by
  have : Fact (IsPGroup p R) := ⟨hR⟩
  have := CFSG.isElementaryAbelian_quotient_frattini (R := R) (p := p)
  exact (IsMulCommutative.is_comm).comm a b

private theorem stepBAction_frattini_pow {R : Type*} [Group R] [Finite R] {p : ℕ}
    [Fact p.Prime] (hR : IsPGroup p R) (a : R ⧸ frattini R) : a ^ p = 1 := by
  have : Fact (IsPGroup p R) := ⟨hR⟩
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
  exact CFSG.pth_power_mem_frattini_of_isPGroup a

private theorem stepBAction_eq_one_of_fixed {V : Type*} [Group V] (hV : ∀ a : V, a ^ 2 = 1)
    {σ : MulAut V} (hσ : σ ^ 3 = 1) (u : V) (hfix : σ (σ u * u⁻¹) = σ u * u⁻¹) :
    σ u * u⁻¹ = 1 := by
  have h3 : σ (σ (σ u)) = u := by
    have := DFunLike.congr_fun hσ u
    simpa [pow_succ, MulAut.mul_apply] using this
  have hprod : σ (σ (σ u * u⁻¹)) * σ (σ u * u⁻¹) * (σ u * u⁻¹) = 1 := by
    simp only [map_mul, map_inv, h3]
    group
  rw [hfix, hfix] at hprod
  have h2 := hV (σ u * u⁻¹)
  rw [pow_two] at h2
  rwa [h2, one_mul] at hprod

private def stepBActionTrivMod {V : Type*} [Group V] (W : Subgroup V) : Subgroup (MulAut V) where
  carrier := {τ | ∀ u, τ u * u⁻¹ ∈ W}
  one_mem' := fun u => by simp
  mul_mem' := fun {a b} ha hb u => by
    have h := W.mul_mem (ha (b u)) (hb u)
    simpa [MulAut.mul_apply, mul_assoc] using h
  inv_mem' := fun {a} ha u => by
    simpa using W.inv_mem (ha (a⁻¹ u))

private noncomputable abbrev stepBActionOnS {P S : Subgroup G}
    (hPS : P ≤ normalizer (S : Set G)) : MulDistribMulAction P S :=
  MulDistribMulAction.compHom S (S.normalizerMonoidHom.comp (Subgroup.inclusion hPS))

private noncomputable abbrev stepBActionOnV {P S : Subgroup G}
    (hPS : P ≤ normalizer (S : Set G)) : MulDistribMulAction P (S ⧸ frattini S) :=
  letI := stepBActionOnS hPS
  CFSG.PreuniquenessRankFour.Helpers.characteristic_quotient_mulDistribMulAction (frattini S)

private noncomputable abbrev stepBActionRep {P S : Subgroup G}
    (hPS : P ≤ normalizer (S : Set G)) : P →* MulAut (S ⧸ frattini S) :=
  letI := stepBActionOnV hPS
  MulDistribMulAction.toMulAut P (S ⧸ frattini S)

private theorem stepBActionRep_injective {P S : Subgroup G} (hPS : P ≤ normalizer (S : Set G))
    (hP : IsPGroup 3 P) (hS : IsPGroup 2 S)
    (hinj : Function.Injective (@MulDistribMulAction.toMulAut P S _ _ (stepBActionOnS hPS))) :
    Function.Injective (stepBActionRep hPS) := by
  let _ := stepBActionOnS hPS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact CFSG.PreuniquenessRankFour.Helpers.faithful_coprime_pGroup_action_on_frattini_quotient 3
    hP (stepBAction_not_three_dvd_card (hS.to_subgroup _)) hinj

private theorem stepBAction_injective_on_S {P S : Subgroup G} (hPS : P ≤ normalizer (S : Set G))
    (hP : IsPGroup 3 P) {z : G} (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hcenter : ∀ w ∈ P, w ∈ centralizer (P : Set G) → w ^ 3 = 1 → w ∈ zpowers z)
    (hzS : z ∉ centralizer (S : Set G)) :
    Function.Injective (@MulDistribMulAction.toMulAut P S _ _ (stepBActionOnS hPS)) := by
  let _ := stepBActionOnS hPS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := MulDistribMulAction.toMulAut P S
  rw [← MonoidHom.ker_eq_bot_iff]
  by_contra hK
  have : Group.IsNilpotent P := hP.isNilpotent
  have hKZ := Group.IsNilpotent.inf_center_ne_bot_of_normal hK
  have : Nontrivial ↥(ρ.ker ⊓ center P) := (nontrivial_iff_ne_bot _).mpr hKZ
  obtain ⟨n, hn, hcard⟩ :=
    ((hP.to_subgroup (ρ.ker ⊓ center P)).nontrivial_iff_card).mp inferInstance
  obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card' (G := ↥(ρ.ker ⊓ center P)) 3
    (by rw [hcard]; exact dvd_pow_self 3 hn.ne')
  have hwo : orderOf ((w : P) : G) = 3 := by rw [orderOf_coe, orderOf_coe, hw]
  have hwc : ((w : P) : G) ∈ centralizer (P : Set G) := by
    rw [mem_centralizer_iff]
    intro g hg
    exact congrArg Subtype.val (mem_center_iff.mp w.2.2 ⟨g, hg⟩)
  have hw3 : ((w : P) : G) ^ 3 = 1 := by rw [← hwo]; exact pow_orderOf_eq_one _
  have hwz := hcenter _ (w : P).2 hwc hw3
  have hzw : z ∈ zpowers ((w : P) : G) := by
    have h : zpowers ((w : P) : G) = zpowers z := by
      refine Subgroup.eq_of_le_of_card_ge (zpowers_le.mpr hwz) ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, hwo, orderOf_eq_prime hz3 hz1]
    rw [h]
    exact mem_zpowers z
  have hwS : ((w : P) : G) ∈ centralizer (S : Set G) := by
    rw [mem_centralizer_iff]
    intro s hs
    have h1 : ρ (w : P) = 1 := w.2.1
    have h2 : (ρ (w : P) ⟨s, hs⟩ : G) = ((1 : MulAut S) ⟨s, hs⟩ : G) := by rw [h1]
    change ((w : P) : G) * s * ((w : P) : G)⁻¹ = s at h2
    exact (mul_inv_eq_iff_eq_mul.mp h2).symm
  exact hzS (zpowers_le.mpr hwS hzw)

omit [Finite G] in
private theorem stepBAction_exists_eq_mul_inv {P S : Subgroup G}
    (hPS : P ≤ normalizer (S : Set G)) (hcomm : ∀ a b : S ⧸ frattini S, a * b = b * a) {z : G}
    (hz : z ∈ P) (hSZ : ⁅S, zpowers z⁆ = S) (v : S ⧸ frattini S) :
    ∃ u, v = stepBActionRep hPS ⟨z, hz⟩ u * u⁻¹ := by
  set σ := stepBActionRep hPS ⟨z, hz⟩
  let β : (S ⧸ frattini S) →* (S ⧸ frattini S) :=
    MonoidHom.mk' (fun u => σ u * u⁻¹) (fun a b => by
      rw [map_mul, mul_inv_rev, mul_assoc, mul_assoc, ← mul_assoc (σ b), hcomm (σ b * b⁻¹),
        hcomm (σ b)])
  let W := β.range
  have hz' : (⟨z, hz⟩ : P) ∈ (stepBActionTrivMod W).comap (stepBActionRep hPS) :=
    fun u => ⟨u, rfl⟩
  have hZle : zpowers z ≤ ((stepBActionTrivMod W).comap (stepBActionRep hPS)).map P.subtype :=
    zpowers_le.mpr ⟨⟨z, hz⟩, hz', rfl⟩
  have hle : ⁅zpowers z, S⁆ ≤ (W.comap (QuotientGroup.mk' (frattini S))).map S.subtype := by
    rw [commutator_le]
    intro w hw s hs
    obtain ⟨p, hp, rfl⟩ := hZle hw
    refine ⟨⟨(p : G) * s * (p : G)⁻¹, (mem_normalizer_iff.mp (hPS p.2) s).mp hs⟩ * ⟨s, hs⟩⁻¹,
      ?_, rfl⟩
    rw [SetLike.mem_coe, mem_comap, map_mul, map_inv]
    exact hp (QuotientGroup.mk' (frattini S) ⟨s, hs⟩)
  obtain ⟨s, rfl⟩ := QuotientGroup.mk'_surjective (frattini S) v
  have hs : (s : G) ∈ (W.comap (QuotientGroup.mk' (frattini S))).map S.subtype := by
    apply hle
    rw [commutator_comm, hSZ]
    exact s.2
  obtain ⟨s', hs', hss'⟩ := hs
  obtain rfl : s' = s := Subtype.ext hss'
  obtain ⟨u, hu⟩ := hs'
  exact ⟨u, hu.symm⟩

private theorem stepBAction_exists_lift {P S : Subgroup G} (hPS : P ≤ normalizer (S : Set G))
    (hP : IsPGroup 3 P) (hS : IsPGroup 2 S) {x : G} (hx : x ∈ P) (v : S ⧸ frattini S)
    (hv : stepBActionRep hPS ⟨x, hx⟩ v = v) :
    ∃ s : S, (s : G) ∈ centralizer ({x} : Set G) ∧ (s : S ⧸ frattini S) = v := by
  let _ := stepBActionOnS hPS
  let _ := stepBActionOnV hPS
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs, hfix⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.fixedPoint_lifts_of_prime_coprime_kernel
      (acting := zpowers (⟨x, hx⟩ : P)) 3 (hP.to_subgroup _) (QuotientGroup.mk' (frattini S))
      (QuotientGroup.mk'_surjective _) (fun _ _ => rfl)
      (by rw [QuotientGroup.ker_mk']; exact stepBAction_not_three_dvd_card (hS.to_subgroup _)) v
      (fun a => (zpowers_le.mpr (show (⟨x, hx⟩ : P) ∈ MulAction.stabilizer P v from hv)) a.2)
  refine ⟨s, ?_, hs⟩
  have h : x * (s : G) * x⁻¹ = s := congrArg Subtype.val (hfix ⟨⟨x, hx⟩, mem_zpowers _⟩)
  rw [mem_centralizer_singleton_iff]
  exact (mul_inv_eq_iff_eq_mul.mp h).symm

private theorem stepBAction_nearCyclic {P S T : Subgroup G} (hPS : P ≤ normalizer (S : Set G))
    (hP : IsPGroup 3 P) (hS : IsPGroup 2 S) (hST : S ≤ T) {x : G} (hx : x ∈ P)
    (hnear : NearCyclic ↥(T ⊓ centralizer ({x} : Set G))) :
    NearCyclic ↥(fixedSubgroup (stepBActionRep hPS) ⟨x, hx⟩) := by
  have h1 : NearCyclic ↥(S ⊓ centralizer ({x} : Set G)) :=
    NearCyclic.of_injective (Subgroup.inclusion (inf_le_inf_right _ hST))
      (Subgroup.inclusion_injective _) hnear
  let f : ↥(S ⊓ centralizer ({x} : Set G)) →* ↥(fixedSubgroup (stepBActionRep hPS) ⟨x, hx⟩) :=
    ((QuotientGroup.mk' (frattini S)).comp (Subgroup.inclusion inf_le_left)).codRestrict _
      (fun s => by
        have hs : (s : G) * x = x * s := mem_centralizer_singleton_iff.mp s.2.2
        change QuotientGroup.mk' (frattini S) ⟨x * s * x⁻¹, _⟩ =
          QuotientGroup.mk' (frattini S) ⟨s, s.2.1⟩
        congr 2
        rw [← hs, mul_inv_cancel_right])
  refine NearCyclic.of_surjective f ?_ h1
  rintro ⟨v, hv⟩
  obtain ⟨s, hsx, rfl⟩ := stepBAction_exists_lift hPS hP hS hx v hv
  exact ⟨⟨s, s.2, hsx⟩, rfl⟩

theorem exists_faithful_two_group_action (hS : Setting G) {P : Sylow 3 G} {M : Subgroup G}
    (hs : SmallRankSituation G 3 P M) {x z g : G} {T : Subgroup G}
    (hd : SmallRank3Data P M x z g T) :
    ∃ (V : Type) (_ : Group V) (_ : Finite V) (ρ : (P : Subgroup G) →* MulAut V),
      (∀ a b : V, a * b = b * a) ∧ (∀ a : V, a ^ 2 = 1) ∧ Function.Injective ρ ∧
      (∀ v : V, ρ ⟨z, hd.central.mem⟩ v = v → v = 1) ∧
      NearCyclic ↥(fixedSubgroup ρ ⟨x, hd.point.mem⟩) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzT : z ∈ normalizer (T : Set G) := hd.sylowTwo.normalized hd.central.mem
  have hST : ⁅T, zpowers z⁆ ≤ T := stepBAction_commutator_le hzT
  have hS2 : IsPGroup 2 ↥(⁅T, zpowers z⁆ : Subgroup G) := hd.sylowTwo.isPGroup.to_le hST
  have hPS := stepBAction_le_normalizer hd.sylowTwo.normalized hd.central.centralizes
  have hidem : ⁅⁅T, zpowers z⁆, zpowers z⁆ = ⁅T, zpowers z⁆ :=
    stepBAction_commutator_idem hd.sylowTwo.isPGroup
      (P.isPGroup'.to_le (zpowers_le.mpr hd.central.mem)) hzT
  have hcomm := stepBAction_frattini_comm hS2
  have hpow := stepBAction_frattini_pow hS2
  have hσ : stepBActionRep hPS ⟨z, hd.central.mem⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h : (⟨z, hd.central.mem⟩ : (P : Subgroup G)) ^ 3 = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow]; exact hd.central.pow_eq_one)
    rw [h, map_one]
  refine ⟨↥(⁅T, zpowers z⁆) ⧸ frattini ↥(⁅T, zpowers z⁆), inferInstance, inferInstance,
    stepBActionRep hPS, hcomm, hpow, ?_, ?_,
    stepBAction_nearCyclic hPS P.isPGroup' hS2 hST hd.point.mem hd.near⟩
  · exact stepBActionRep_injective hPS P.isPGroup' hS2
      (stepBAction_injective_on_S hPS P.isPGroup' hd.central.pow_eq_one hd.central.ne_one
        (SmallRankPlane.of_situation hS hs hd.point hd.central).center
        (stepBAction_not_mem_centralizer hidem hd.noncentral))
  · intro v hv
    obtain ⟨u, rfl⟩ := stepBAction_exists_eq_mul_inv hPS hcomm hd.central.mem hidem v
    exact stepBAction_eq_one_of_fixed hpow hσ u hv

end CFSG.LocalAnalysis.RankThreeTheoremC
