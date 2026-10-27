module

public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerTwoGroups
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeAmbientCentralizerGeneration
import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
import CFSG.LocalAnalysis.RankThreeUC.TheoremDClauseCCore

public section

namespace CFSG.LocalAnalysis.RankThreeTheoremC

open CFSG.Open CFSG.RankThreeCoreUniqueness.Helpers CFSG.GorensteinWalter CFSG.ABGLocalTools
  Subgroup
open scoped MatrixGroups

section Psl2

variable {K : Type} [Field K]

theorem eq_bot_of_coprime_of_le_normalizer [Finite K] {p : ℕ} [Fact p.Prime] [CharP K p]
    (hK : Nat.card K = p ^ 2) {W : Subgroup (PSL2 K)} (hcop : ¬ p ∣ Nat.card W)
    (hN : psl2UpperUnipotentSubgroup K ≤ normalizer (W : Set (PSL2 K))) : W = ⊥ := by
  have hpow : ∀ u : psl2UpperUnipotentSubgroup K, u ^ p = 1 := by
    rintro ⟨u, hu⟩
    obtain ⟨a, rfl⟩ := (mem_psl2UpperUnipotentSubgroup_iff u).1 hu
    exact Subtype.ext (psl2Root_pow_prime a)
  have hcard : Nat.card (psl2UpperUnipotentSubgroup K) = p ^ 2 := by
    rw [psl2UpperUnipotentSubgroup_card, hK]
  have hgen := CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p
    Fact.out (psl2UpperUnipotentSubgroup K) W hpow hcard hcop hN
  have hUp : IsPGroup p (psl2UpperUnipotentSubgroup K) := IsPGroup.of_card hcard
  have hcopWU : Nat.Coprime (Nat.card W) (Nat.card (psl2UpperUnipotentSubgroup K)) := by
    rw [hcard]
    exact (((Nat.Prime.coprime_iff_not_dvd Fact.out).2 hcop).pow_left 2).symm
  have hdisj : Disjoint W (psl2UpperUnipotentSubgroup K) := by
    refine Subgroup.disjoint_def.mpr fun {g} hgW hgU => ?_
    have h1 : orderOf g ∣ Nat.card W := by
      have := Subgroup.orderOf_dvd_natCard W hgW
      simpa using this
    have h2 : orderOf g ∣ Nat.card (psl2UpperUnipotentSubgroup K) := by
      have := Subgroup.orderOf_dvd_natCard (psl2UpperUnipotentSubgroup K) hgU
      simpa using this
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcopWU h1 h2)
  rw [hgen]
  refine le_bot_iff.mp (iSup_le fun u => iSup_le fun hu1 g hg => ?_)
  obtain ⟨a, ha⟩ := (mem_psl2UpperUnipotentSubgroup_iff _).1 u.2
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hu1 (Subtype.ext (by simpa using ha))
  have hgc : g * psl2Root a = psl2Root a * g := by
    have := mem_centralizer_singleton_iff.mp hg.2
    rw [ha] at this
    exact this
  have hgU := mem_upperUnipotent_of_commute ha0 hgc
  exact Subgroup.disjoint_def.mp hdisj hg.1 hgU

end Psl2

section Transport

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_of_coprime_of_le_normalizer_isSylowOf_psl {p : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Finite K] [CharP K p] (hK : Nat.card K = p ^ 2)
    {L U : Subgroup G} (e : L ≃* PSL2 K) (hU : IsSylowOf p U L) {W : Subgroup G} (hWL : W ≤ L)
    (hcop : ¬ p ∣ Nat.card W) (hN : U ≤ normalizer (W : Set G)) : W = ⊥ := by
  obtain ⟨e', he'⟩ := exists_mulEquiv_of_isSylowOf_psl hK e hU
  set W' : Subgroup (PSL2 K) := (W.subgroupOf L).map e'.toMonoidHom with hW'
  have hW'mem : ∀ w : L, e' w ∈ W' ↔ (w : G) ∈ W := fun w => by
    rw [hW', Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    exact Iff.rfl
  have hcop' : ¬ p ∣ Nat.card W' := by
    have h1 : Nat.card W' = Nat.card (W.subgroupOf L) :=
      Subgroup.card_map_of_injective e'.injective
    have h2 : Nat.card (W.subgroupOf L) = Nat.card W :=
      Nat.card_congr (subgroupOfEquivOfLe hWL).toEquiv
    rw [h1, h2]
    exact hcop
  have hN' : psl2UpperUnipotentSubgroup K ≤ normalizer (W' : Set (PSL2 K)) := by
    intro ũ hũ
    obtain ⟨u, rfl⟩ := e'.surjective ũ
    have hu : (u : G) ∈ U := (he' u).2 hũ
    have hu' := Subgroup.mem_normalizer_iff.mp (hN hu)
    rw [Subgroup.mem_normalizer_iff]
    intro w
    obtain ⟨w₀, rfl⟩ := e'.surjective w
    rw [← map_inv, ← map_mul, ← map_mul, hW'mem, hW'mem]
    simpa using hu' (w₀ : G)
  have hbot := eq_bot_of_coprime_of_le_normalizer hK hcop' hN'
  rw [eq_bot_iff]
  intro w hw
  have hwL : w ∈ L := hWL hw
  have : e' ⟨w, hwL⟩ ∈ W' := (hW'mem _).2 hw
  rw [hbot, Subgroup.mem_bot] at this
  have h1 := e'.injective (this.trans (map_one e').symm)
  exact congrArg Subtype.val h1

theorem le_centralizer_of_coprime_of_le_normalizer_layer {p : ℕ} [Fact p.Prime]
    {K : Type} [Field K] [Finite K] [CharP K p] (hK : Nat.card K = p ^ 2)
    {C L U X : Subgroup G} (e : L ≃* PSL2 K) (hU : IsSylowOf p U L)
    (hCL : C ≤ normalizer (L : Set G)) (hXC : X ≤ C) (hcop : ¬ p ∣ Nat.card X)
    (hN : U ≤ normalizer (X : Set G)) : X ≤ centralizer (L : Set G) := by
  have hUL : U ≤ normalizer (L : Set G) := hU.le.trans Subgroup.le_normalizer
  have h1 : X ⊓ L = ⊥ := eq_bot_of_coprime_of_le_normalizer_isSylowOf_psl hK e hU inf_le_right
    (fun h => hcop (h.trans (Subgroup.card_dvd_of_le inf_le_left)))
    (le_normalizer_inf hN hUL)
  have hcomm : ∀ w ∈ X, ∀ u ∈ U, w * u = u * w := by
    intro w hw u hu
    have hwu : w * u * w⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hCL (hXC hw)) u).mp (hU.le hu)
    have hcL : w * u * w⁻¹ * u⁻¹ ∈ L := L.mul_mem hwu (L.inv_mem (hU.le hu))
    have hcX : w * u * w⁻¹ * u⁻¹ ∈ X := by
      have h2 : u * w⁻¹ * u⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hN hu) w⁻¹).mp (X.inv_mem hw)
      simpa [mul_assoc] using X.mul_mem hw h2
    have h3 : w * u * w⁻¹ * u⁻¹ ∈ X ⊓ L := ⟨hcX, hcL⟩
    rw [h1, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
    exact h3
  intro w hw
  obtain ⟨u₀, hu₀U, hu₀⟩ := exists_conj_eq_of_centralizes_isSylowOf_psl hK e hU
    (hCL (hXC hw)) (hcomm w hw)
  have hvL : u₀⁻¹ * w ∈ centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h2 := hu₀ l hl
    calc l * (u₀⁻¹ * w) = u₀⁻¹ * (u₀ * l * u₀⁻¹) * w := by group
      _ = u₀⁻¹ * (w * l * w⁻¹) * w := by rw [h2]
      _ = u₀⁻¹ * w * l := by group
  have hu₀L : u₀ ∈ L := hU.le hu₀U
  have hcomm₀ : Commute u₀ (u₀⁻¹ * w) := Subgroup.mem_centralizer_iff.mp hvL u₀ hu₀L
  have hn : Nat.Coprime p (orderOf w) := by
    have hdvd : orderOf w ∣ Nat.card X := by
      have := Subgroup.orderOf_dvd_natCard X hw
      simpa using this
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).2 fun h => hcop (h.trans hdvd)
  have hpow : u₀ ^ (orderOf w) = 1 := by
    have h2 : (u₀ * (u₀⁻¹ * w)) ^ (orderOf w) = u₀ ^ (orderOf w) * (u₀⁻¹ * w) ^ (orderOf w) :=
      hcomm₀.mul_pow _
    rw [mul_inv_cancel_left, pow_orderOf_eq_one] at h2
    have h3 : u₀ ^ (orderOf w) = ((u₀⁻¹ * w) ^ (orderOf w))⁻¹ :=
      eq_inv_of_mul_eq_one_left h2.symm
    refine eq_one_of_commute_of_mulEquiv_psl_two e (L.pow_mem hu₀L _) fun h hh => ?_
    rw [h3]
    have h4 : (u₀⁻¹ * w) ^ (orderOf w) ∈ centralizer (L : Set G) :=
      (centralizer (L : Set G)).pow_mem hvL _
    have h5 := (centralizer (L : Set G)).inv_mem h4
    rw [Subgroup.mem_centralizer_iff] at h5
    exact h5 h hh
  have hu₀1 : u₀ = 1 := by
    have h1' : orderOf u₀ ∣ p :=
      orderOf_dvd_of_pow_eq_one (pow_eq_one_of_mem_isSylowOf_psl hK e hU hu₀U)
    have h2' : orderOf u₀ ∣ orderOf w := orderOf_dvd_of_pow_eq_one hpow
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hn h1' h2')
  rw [hu₀1, inv_one, one_mul] at hvL
  exact hvL

end Transport

section Generic

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_layer_of_coprime_of_isGenericPoint
    {p : ℕ} [Fact p.Prime] {P : Sylow p G} {M : Subgroup G}
    {x : G} (hx : IsGenericPoint p P M x) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m))
    {X : Subgroup G} (hXC : X ≤ centralizer ({x} : Set G)) (hcop : ¬ p ∣ Nat.card X)
    (hN : ((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓
      rankThreeLayer (centralizer ({x} : Set G)) ≤ normalizer (X : Set G)) :
    X ≤ centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G) := by
  obtain ⟨hxP, hxL, hsyl, hrk⟩ := id hx
  obtain ⟨-, hx1, hxp, -, hxCM⟩ := hxL
  obtain ⟨hm2, -⟩ := eq_two_of_isSylowOf_mulEquiv_psl hsyl (rankThreeLayer_le _)
    (le_normalizer_rankThreeLayer _) ⟨hxP, mem_centralizer_singleton_iff.mpr rfl⟩ hx1 hxp
    (fun c hc => mem_centralizer_singleton_iff.mp hc) hrk.le hm e
  subst hm2
  have hK : Nat.card (GaloisField p 2) = p ^ 2 := GaloisField.card p 2 (by norm_num)
  have hU : IsSylowOf p (((P : Subgroup G) ⊓ centralizer ({x} : Set G)) ⊓
      rankThreeLayer (centralizer ({x} : Set G))) (rankThreeLayer (centralizer ({x} : Set G))) :=
    hsyl.inf_of_le_normalizer (rankThreeLayer_le _) (le_normalizer_rankThreeLayer _)
  exact le_centralizer_of_coprime_of_le_normalizer_layer hK e hU
    (le_normalizer_rankThreeLayer _) hXC hcop hN

theorem primeCore_inf_centralizer_le_centralizer_layer (hS : Setting G) {p : ℕ} [Fact p.Prime]
    (hp : p ∈ rankThreeSigmaA G) {P : Sylow p G} {M : Subgroup G}
    (hM : IsCoreMaxLocal p P M) {x : G} (hx : IsGenericPoint p P M x) {m : ℕ} (hm : 2 ≤ m)
    (e : rankThreeLayer (centralizer ({x} : Set G)) ≃* PSL(2, GaloisField p m)) :
    rankThreePrimeCore p M ⊓ centralizer ({x} : Set G) ≤
      centralizer ((rankThreeLayer (centralizer ({x} : Set G)) : Subgroup G) : Set G) := by
  obtain ⟨hPM, -⟩ := sylow_le_of_isCoreMaxLocal hS hp hM
  obtain ⟨hNM, hMN, hNcop⟩ := CFSG.LocalAnalysis.RankThreeUC.rankThreePrimeCore_spec p M
  refine le_centralizer_layer_of_coprime_of_isGenericPoint hx hm e inf_le_right ?_ ?_
  · intro hdvd
    exact (Nat.Prime.coprime_iff_not_dvd Fact.out).1 hNcop
      (hdvd.trans (Subgroup.card_dvd_of_le inf_le_left))
  ·
    refine le_trans (le_inf ?_ ?_) inf_normalizer_le_normalizer_inf
    · exact (inf_le_left.trans (inf_le_left.trans hPM)).trans hMN
    · exact (inf_le_left.trans inf_le_right).trans Subgroup.le_normalizer

end Generic

end CFSG.LocalAnalysis.RankThreeTheoremC
