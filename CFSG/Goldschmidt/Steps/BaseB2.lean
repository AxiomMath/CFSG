module

public import CFSG.Goldschmidt.StatementsH
import CFSG.Goldschmidt.Steps.AbelSyl
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
import CFSG.Milestones.OO_odd_order_solvable
public import CFSG.Goldschmidt.Statements

public section

namespace CFSG.Goldschmidt

open CFSG.Open CFSG.ComponentClassification
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)
open scoped commutatorElement

section Helpers

private theorem isPGroup_center_of_oddCore {Q : Type*} [Group Q] [Finite Q]
    (hO : goldschmidtOddCore Q = ⊥) : IsPGroup 2 (Subgroup.center Q) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  rw [Subgroup.orderOf_mk]
  obtain ⟨k, m, hm, hkm⟩ := Nat.exists_eq_two_pow_mul_odd (n := orderOf g) (orderOf_pos g).ne'
  refine ⟨k, ?_⟩
  have hy : orderOf (g ^ (2 ^ k)) = m := by
    rw [orderOf_pow_of_dvd (pow_ne_zero _ two_ne_zero) (hkm ▸ dvd_mul_right _ _), hkm,
      Nat.mul_div_cancel_left _ (pow_pos two_pos _)]
  have hnormal : (Subgroup.zpowers (g ^ (2 ^ k))).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr (Subgroup.pow_mem _ hg _))
  have hodd : Odd (Nat.card (Subgroup.zpowers (g ^ (2 ^ k)))) := by
    rw [Nat.card_zpowers, hy]
    exact hm
  have hle : Subgroup.zpowers (g ^ (2 ^ k)) ≤ goldschmidtOddCore Q := le_sSup ⟨hnormal, hodd⟩
  rw [hO] at hle
  have h1 : g ^ (2 ^ k) = 1 := Subgroup.mem_bot.mp (hle (Subgroup.mem_zpowers _))
  rw [h1, orderOf_one] at hy
  rw [hkm, ← hy, mul_one]

private theorem isComponentOf_top_of {Q : Type*} [Group Q] (hq : CFSG.Open.IsQuasisimple Q) :
    IsComponentOf (⊤ : Subgroup Q) ⊤ :=
  ⟨le_rfl, CFSG.Open.IsSubnormal.refl ⊤, Components.quasisimple_of_equiv Subgroup.topEquiv hq⟩

private theorem eq_top_of_isComponentOf {Q : Type*} [Group Q] (hq : CFSG.Open.IsQuasisimple Q)
    {K : Subgroup Q} (hK : IsComponentOf K ⊤) : K = ⊤ := by
  rcases Quasisimple.subnormal_le_center_or_eq_top hq K hK.2.1 with h | h
  · have : Group.IsPerfect K := ⟨hK.2.2.1⟩
    exact absurd (Quasisimple.perfect_le_center_eq_bot K h)
      (K.nontrivial_iff_ne_bot.mp (Quasisimple.nontrivial hK.2.2))
  · exact h

private theorem pCore_eq_center_of {Q : Type*} [Group Q] [Finite Q] (hq : CFSG.Open.IsQuasisimple Q)
    (hO : goldschmidtOddCore Q = ⊥) : CFSG.Open.pCore 2 Q = Subgroup.center Q := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : (CFSG.Open.pCore 2 Q).Normal := CFSG.RankThreeCoreUniqueness.Helpers.pCore_normal 2
  refine le_antisymm ?_ (CFSG.RankThreeCoreUniqueness.Helpers.normal_pGroup_le_pCore 2 _
    inferInstance (isPGroup_center_of_oddCore hO))
  rcases Quasisimple.normal_le_center_or_eq_top hq (CFSG.Open.pCore 2 Q) with h | h
  · exact h
  · exfalso
    have hp : IsPGroup 2 (⊤ : Subgroup Q) :=
      h ▸ CFSG.RankThreeCoreUniqueness.Helpers.pCore_isPGroup 2
    have := (hp.of_equiv Subgroup.topEquiv).isNilpotent
    have : Group.IsPerfect Q := ⟨hq.1⟩
    have : Nontrivial Q := Quasisimple.nontrivial hq
    exact Group.IsPerfect.not_isSolvable Q inferInstance

private theorem goldschmidtSimpleType_congr {L L' : Type} [Group L] [Group L'] (e : L ≃* L')
    (h : goldschmidtSimpleType L) : goldschmidtSimpleType L' := by
  unfold goldschmidtSimpleType at h ⊢
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨n, hn, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ |
      ⟨p, f, hp, hodd, hf, h5, h8, ⟨e'⟩⟩ | ⟨k, hk, hcard⟩ | ⟨⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨n, hn, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨p, f, hp, hodd, hf, h5, h8, ⟨e.symm.trans e'⟩⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨k, hk, (Nat.card_congr e.symm.toEquiv).trans hcard⟩))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨e.symm.trans e'⟩))))

private theorem coreConclusion_iff {Q : Type} [Group Q] [Finite Q] (hq : CFSG.Open.IsQuasisimple Q)
    (hO : goldschmidtOddCore Q = ⊥) (T : Sylow 2 Q) (B : Subgroup Q) :
    CoreConclusion Q T B ↔
      goldschmidtSimpleType (Q ⧸ Subgroup.center Q) ∧
        B = Subgroup.center Q ⊔ Omega1 (T : Subgroup Q) := by
  have hE : goldschmidtLayer Q = ⊤ := top_le_iff.mp (le_sSup (isComponentOf_top_of hq))
  let e : (⊤ : Subgroup Q) ⧸ Subgroup.center (⊤ : Subgroup Q) ≃* Q ⧸ Subgroup.center Q :=
    QuotientGroup.congr _ _ Subgroup.topEquiv (Subgroup.map_center_eq Subgroup.topEquiv)
  have hset : {t | t ∈ (T : Subgroup Q) ⊓ goldschmidtLayer Q ∧ t ^ 2 = 1} =
      {t | t ∈ (T : Subgroup Q) ∧ t ^ 2 = 1} := by
    rw [hE, inf_top_eq]
  unfold CoreConclusion
  rw [hset, hE, pCore_eq_center_of hq hO]
  constructor
  · rintro ⟨-, hB, hK⟩
    exact ⟨goldschmidtSimpleType_congr e (hK ⊤ (isComponentOf_top_of hq)), hB⟩
  · rintro ⟨ht, hB⟩
    refine ⟨sup_top_eq _, hB, fun K hK => ?_⟩
    obtain rfl := eq_top_of_isComponentOf hq hK
    exact goldschmidtSimpleType_congr e.symm ht

private theorem sq_eq_one_of_mem_omega1 {Q : Type*} [Group Q] {T : Subgroup Q}
    (hT : IsMulCommutative (Omega1 T)) {u : Q} (hu : u ∈ Omega1 T) : u ^ 2 = 1 := by
  induction hu using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    have hxy : x * y = y * x := congrArg Subtype.val (hT.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    calc (x * y) ^ 2 = x * (y * x) * y := by simp only [sq]; group
      _ = x * (x * y) * y := by rw [hxy]
      _ = x ^ 2 * y ^ 2 := by simp only [sq]; group
      _ = 1 := by rw [ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

private theorem mul_center_comm {G : Type*} [Group G] {a b z w : G} (hab : a * b = b * a)
    (hz : z ∈ Subgroup.center G) (hw : w ∈ Subgroup.center G) :
    a * z * (b * w) = b * w * (a * z) := by
  have h1 := Subgroup.mem_center_iff.mp hz
  have h2 := Subgroup.mem_center_iff.mp hw
  calc a * z * (b * w) = a * (z * b) * w := by group
    _ = a * (b * z) * w := by rw [h1 b]
    _ = a * b * (z * w) := by group
    _ = b * a * (w * z) := by rw [hab, h2 z]
    _ = b * (a * w) * z := by group
    _ = b * (w * a) * z := by rw [h2 a]
    _ = b * w * (a * z) := by group

private theorem mem_commutator_of_mem_center {G : Type*} [Group G] [Finite G] {p : ℕ}
    [hp : Fact p.Prime] (P : Sylow p G) (hperf : commutator G = ⊤) {z : G}
    (hz : z ∈ Subgroup.center G) (hzP : z ∈ (P : Subgroup G)) :
    z ∈ ⁅(P : Subgroup G), (P : Subgroup G)⁆ := by
  have hkey : ∀ (k : ℕ) (g₀ : G), g₀⁻¹ * z ^ k * g₀ ∈ (P : Subgroup G) →
      g₀⁻¹ * z ^ k * g₀ = z ^ k := by
    intro k g₀ _
    rw [mul_assoc, ← Subgroup.mem_center_iff.mp (Subgroup.pow_mem _ hz k) g₀, ← mul_assoc,
      inv_mul_cancel, one_mul]
  let ϕ : (P : Subgroup G) →* Abelianization (P : Subgroup G) := Abelianization.of
  have h1 : ϕ.transfer z = 1 := by
    have hle := Abelianization.commutator_subset_ker ϕ.transfer
    rw [hperf] at hle
    exact MonoidHom.mem_ker.mp (hle (Subgroup.mem_top z))
  rw [MonoidHom.transfer_eq_pow ϕ z hkey] at h1
  have h2 := MonoidHom.mem_ker.mpr h1
  rw [Abelianization.ker_of] at h2
  have h3 : z ^ (P : Subgroup G).index ∈ ⁅(P : Subgroup G), (P : Subgroup G)⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨_, h2, rfl⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp P.isPGroup' ⟨z, hzP⟩
  rw [Subgroup.orderOf_mk] at hk
  have hcop : Nat.gcd (P : Subgroup G).index (orderOf z) = 1 := by
    rw [hk]
    exact Nat.Coprime.pow_right k (Nat.Coprime.symm
      ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr P.not_dvd_index))
  exact Subgroup.zpowers_le.mpr h3 (mem_zpowers_pow_iff.mpr hcop)

end Helpers

theorem B2setup : S_B2setup := by
  intro G _ _ S A hA hIH hq hZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨isPGroup_center_of_oddCore hA.oddCore, ?_⟩
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2
  have : Group.IsPerfect G := ⟨hq.1⟩
  have hperf : Group.IsPerfect (G ⧸ Subgroup.center G) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center G))
      (QuotientGroup.mk'_surjective _)
  have hqbar : CFSG.Open.IsQuasisimple (G ⧸ Subgroup.center G) := Quasisimple.simple_of_perfect _
  have hcen : Subgroup.center (G ⧸ Subgroup.center G) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (G ⧸ Subgroup.center G)) with h | h
    · exact h
    · exfalso
      have : Group.IsPerfect (⊤ : Subgroup (G ⧸ Subgroup.center G)) :=
        Group.IsPerfect.top_iff.mpr hperf
      exact bot_ne_top
        (Quasisimple.perfect_le_center_eq_bot (⊤ : Subgroup (G ⧸ Subgroup.center G)) h.ge).symm
  have hObar : goldschmidtOddCore (G ⧸ Subgroup.center G) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (goldschmidtOddCore (G ⧸ Subgroup.center G)) with h | h
    · exact h
    · exfalso
      have hodd : Odd (Nat.card (G ⧸ Subgroup.center G)) := by
        have h1 : Odd (Nat.card (goldschmidtOddCore (G ⧸ Subgroup.center G))) :=
          OddCore.odd_card (G ⧸ Subgroup.center G)
        rwa [h, Subgroup.card_top] at h1
      exact Group.IsPerfect.not_isSolvable (G ⧸ Subgroup.center G)
        (CFSG.Milestones.odd_order_solvable hodd)
  have hcard : Nat.card (G ⧸ Subgroup.center G) < Nat.card G := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center G)
    have h2 := (Subgroup.one_lt_card_iff_ne_bot (Subgroup.center G)).mpr hZ
    have h3 : 0 < Nat.card (G ⧸ Subgroup.center G) := Nat.card_pos
    rw [h1]
    exact lt_mul_of_one_lt_right h3 h2
  obtain ⟨Sbar, hSbar, hcl⟩ :=
    CFSG.ShultStronglyClosedTI.quotient_stronglyClosed S A (Subgroup.center G) hA.le hA.closed
  have hAS : A.map (QuotientGroup.mk' (Subgroup.center G)) ≤ Sbar := by
    rw [hSbar]
    exact Subgroup.map_mono hA.le
  have hC := hIH (G ⧸ Subgroup.center G) hcard Sbar _ hAS (isMulCommutative_map hA.comm _) hcl
    (normalClosure_map_eq_top hA.gen _ (QuotientGroup.mk'_surjective _)) hObar
  obtain ⟨htype, hAbar⟩ := (coreConclusion_iff hqbar hObar Sbar _).mp hC
  refine ⟨goldschmidtSimpleType_congr
    ((QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot) htype, ?_⟩
  rw [hAbar, hcen, bot_sup_eq, hSbar]

theorem N26_of (h11a : S_N11a) : S_N26 := by
  intro G _ _ S A hA hq hZ htype hAbar hSab
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2
  have hZS : Subgroup.center G ≤ (S : Subgroup G) :=
    (isPGroup_center_of_oddCore hA.oddCore).le_sylow_of_normal S
  let Sbar : Sylow 2 (G ⧸ Subgroup.center G) :=
    S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center G))
  have hSbar : (Sbar : Subgroup (G ⧸ Subgroup.center G)) =
      (S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G)) :=
    Sylow.coe_mapSurjective _ _
  have hΩ : Omega1 (Sbar : Subgroup (G ⧸ Subgroup.center G)) =
      A.map (QuotientGroup.mk' (Subgroup.center G)) := by
    rw [hSbar, hAbar]
  have hOm : IsMulCommutative (Omega1 (Sbar : Subgroup (G ⧸ Subgroup.center G))) := by
    rw [hΩ]
    exact isMulCommutative_map hA.comm _
  have hel := (h11a (G ⧸ Subgroup.center G) htype Sbar hOm).1 (by rw [hSbar]; exact hSab)
  have hSAZ : (S : Subgroup G) ≤ A ⊔ Subgroup.center G := by
    intro s hs
    have hs' : QuotientGroup.mk' (Subgroup.center G) s ∈
        (Sbar : Subgroup (G ⧸ Subgroup.center G)) := by
      rw [hSbar]
      exact Subgroup.mem_map_of_mem _ hs
    have h1 : QuotientGroup.mk' (Subgroup.center G) s ∈
        Omega1 (Sbar : Subgroup (G ⧸ Subgroup.center G)) :=
      Subgroup.subset_closure ⟨hs', hel _ hs'⟩
    rw [hΩ] at h1
    have h2 : s ∈ (A.map (QuotientGroup.mk' (Subgroup.center G))).comap
        (QuotientGroup.mk' (Subgroup.center G)) := h1
    rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk'] at h2
  have hSab' : IsMulCommutative (S : Subgroup G) := by
    refine ⟨⟨fun x y => Subtype.ext ?_⟩⟩
    obtain ⟨a, ha, z, hz, hx⟩ := Subgroup.mem_sup_of_normal_right.mp (hSAZ x.2)
    obtain ⟨b, hb, w, hw, hy⟩ := Subgroup.mem_sup_of_normal_right.mp (hSAZ y.2)
    have hab : a * b = b * a := congrArg Subtype.val (hA.comm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    show (x : G) * y = y * x
    rw [← hx, ← hy]
    exact mul_center_comm hab hz hw
  obtain ⟨H, -, -, -, hfoc, hdisj, -, -⟩ := N7 G S hSab'
  rw [hq.1, inf_top_eq] at hfoc
  apply hZ
  rw [eq_bot_iff, ← hdisj]
  intro z hz
  refine ⟨⟨hZS hz, Subgroup.mem_centralizer_iff.mpr fun h _ => Subgroup.mem_center_iff.mp hz h⟩,
    ?_⟩
  rw [← hfoc]
  exact hZS hz

theorem N27_of (h11a : S_N11a) (h11c : S_N11c) (h13 : S_N13) : S_N27 := by
  intro G _ _ S A hA hq htype hAbar hSnab
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2
  have hZS : Subgroup.center G ≤ (S : Subgroup G) :=
    (isPGroup_center_of_oddCore hA.oddCore).le_sylow_of_normal S
  let Sbar : Sylow 2 (G ⧸ Subgroup.center G) :=
    S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center G))
  have hSbar : (Sbar : Subgroup (G ⧸ Subgroup.center G)) =
      (S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G)) :=
    Sylow.coe_mapSurjective _ _
  have hΩ : Omega1 (Sbar : Subgroup (G ⧸ Subgroup.center G)) =
      A.map (QuotientGroup.mk' (Subgroup.center G)) := by
    rw [hSbar, hAbar]
  have hOm : IsMulCommutative (Omega1 (Sbar : Subgroup (G ⧸ Subgroup.center G))) := by
    rw [hΩ]
    exact isMulCommutative_map hA.comm _
  have hB := (h11a (G ⧸ Subgroup.center G) htype Sbar hOm).2 (by rw [hSbar]; exact hSnab)
  obtain ⟨hOmZ, hcommZ⟩ := h11c (G ⧸ Subgroup.center G) hB Sbar
  by_contra hZA
  have hconjS : ∀ s ∈ (S : Subgroup G), ∀ a ∈ A, s⁻¹ * a * s ∈ A :=
    fun s hs a ha => conj_mem_of_stronglyClosed hA.le hA.closed hs ha
  have hSc : ((S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G))).comap
      (QuotientGroup.mk' (Subgroup.center G)) = S := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZS]
  have hAc : (A.map (QuotientGroup.mk' (Subgroup.center G))).comap
      (QuotientGroup.mk' (Subgroup.center G)) = A ⊔ Subgroup.center G := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  have hSS : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ A ⊔ Subgroup.center G := by
    rw [← hAc, ← Subgroup.map_le_iff_le_comap, Subgroup.map_commutator, ← hSbar, ← hΩ, hOmZ]
    exact hcommZ
  obtain ⟨M, hAM, hM2⟩ : ∃ M : Subgroup G, A ≤ M ∧
      (M.subgroupOf (A ⊔ Subgroup.center G)).index = 2 := by
    have hp : IsPGroup 2 (A ⊔ Subgroup.center G : Subgroup G) :=
      S.isPGroup'.to_le (sup_le hA.le hZS)
    obtain ⟨b, hb⟩ := hp.exists_card_eq
    obtain ⟨a, ha⟩ := (hp.to_subgroup (A.subgroupOf (A ⊔ Subgroup.center G))).exists_card_eq
    have hlt : a < b := by
      by_contra hge
      push Not at hge
      apply hZA
      have h1 : A.subgroupOf (A ⊔ Subgroup.center G) = ⊤ :=
        Subgroup.eq_top_of_le_card _ (by rw [ha, hb]; exact Nat.pow_le_pow_right two_pos hge)
      exact le_sup_right.trans (Subgroup.subgroupOf_eq_top.mp h1)
    obtain ⟨K, hK, hAK⟩ := Sylow.exists_subgroup_card_pow_prime_le 2
      (by rw [hb]; exact pow_dvd_pow 2 (Nat.sub_le b 1)) (A.subgroupOf (A ⊔ Subgroup.center G))
      ha (by omega : a ≤ b - 1)
    refine ⟨K.map (A ⊔ Subgroup.center G).subtype, fun x hx =>
      ⟨⟨x, Subgroup.mem_sup_left hx⟩, hAK hx, rfl⟩, ?_⟩
    rw [show (K.map (A ⊔ Subgroup.center G).subtype).subgroupOf (A ⊔ Subgroup.center G) = K from
      Subgroup.comap_map_eq_self_of_injective (A ⊔ Subgroup.center G).subtype_injective K]
    have h1 := K.card_mul_index
    rw [hK, hb] at h1
    have h2 : 2 ^ b = 2 ^ (b - 1) * 2 := by
      rw [← pow_succ, Nat.sub_add_cancel (by omega : 1 ≤ b)]
    rw [h2] at h1
    exact Nat.eq_of_mul_eq_mul_left (by positivity) h1
  let ψ : G → ZMod 2 := fun g => if g ∈ M then 0 else 1
  have hψmul : ∀ c ∈ A ⊔ Subgroup.center G, ∀ c' ∈ A ⊔ Subgroup.center G,
      ψ (c * c') = ψ c + ψ c' := by
    intro c hc c' hc'
    have h : c * c' ∈ M ↔ (c ∈ M ↔ c' ∈ M) :=
      Subgroup.mul_mem_iff_of_index_two hM2 (a := ⟨c, hc⟩) (b := ⟨c', hc'⟩)
    show (if c * c' ∈ M then (0 : ZMod 2) else 1) =
      (if c ∈ M then 0 else 1) + (if c' ∈ M then 0 else 1)
    by_cases h1 : c ∈ M <;> by_cases h2 : c' ∈ M
    · rw [ite_eq_left (h.mpr (iff_of_true h1 h2)), ite_eq_left h1, ite_eq_left h2, add_zero]
    · rw [ite_eq_right (fun h3 => h2 ((h.mp h3).mp h1)), ite_eq_left h1, ite_eq_right h2, zero_add]
    · rw [ite_eq_right (fun h3 => h1 ((h.mp h3).mpr h2)), ite_eq_right h1, ite_eq_left h2, add_zero]
    · rw [ite_eq_left (h.mpr (iff_of_false h1 h2)), ite_eq_right h1, ite_eq_right h2]
      exact (CharTwo.add_self_eq_zero (1 : ZMod 2)).symm
  have hψA : ∀ a ∈ A, ψ a = 0 := fun a ha => ite_eq_left (hAM ha)
  have hψconj : ∀ n : G, (∀ a ∈ A, n⁻¹ * a * n ∈ A) → ∀ c ∈ A ⊔ Subgroup.center G,
      n⁻¹ * c * n ∈ A ⊔ Subgroup.center G ∧ ψ (n⁻¹ * c * n) = ψ c := by
    intro n hn c hc
    obtain ⟨a, ha, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hc
    have hz' : n⁻¹ * z * n = z := by
      rw [mul_assoc, ← Subgroup.mem_center_iff.mp hz n, ← mul_assoc, inv_mul_cancel, one_mul]
    have he : n⁻¹ * (a * z) * n = (n⁻¹ * a * n) * z := by
      calc n⁻¹ * (a * z) * n = (n⁻¹ * a * n) * (n⁻¹ * z * n) := by group
        _ = (n⁻¹ * a * n) * z := by rw [hz']
    have ha' : n⁻¹ * a * n ∈ A ⊔ Subgroup.center G := Subgroup.mem_sup_left (hn a ha)
    have hzAZ : z ∈ A ⊔ Subgroup.center G := Subgroup.mem_sup_right hz
    rw [he]
    refine ⟨Subgroup.mul_mem _ ha' hzAZ, ?_⟩
    rw [hψmul _ ha' _ hzAZ, hψmul _ (Subgroup.mem_sup_left ha) _ hzAZ, hψA _ (hn a ha),
      hψA _ ha]
  have hconjx : ∀ x ∈ (S : Subgroup G), ∀ c ∈ A ⊔ Subgroup.center G,
      x * c * x⁻¹ ∈ A ⊔ Subgroup.center G ∧ ψ (x * c * x⁻¹) = ψ c := by
    intro x hx c hc
    have h := hψconj x⁻¹ (hconjS x⁻¹ ((S : Subgroup G).inv_mem hx)) c hc
    rwa [inv_inv] at h
  have hcc : ∀ x y z w : G, z ∈ Subgroup.center G → w ∈ Subgroup.center G →
      ⁅x * z, y * w⁆ = ⁅x, y⁆ := by
    intro x y z w hz hw
    have h1 := Subgroup.mem_center_iff.mp hz
    have h2 := Subgroup.mem_center_iff.mp hw
    simp only [commutatorElement_def]
    calc x * z * (y * w) * (x * z)⁻¹ * (y * w)⁻¹
        = x * (z * (y * w)) * z⁻¹ * x⁻¹ * (y * w)⁻¹ := by group
      _ = x * (y * w * z) * z⁻¹ * x⁻¹ * (y * w)⁻¹ := by rw [h1 (y * w)]
      _ = x * y * (w * x⁻¹) * w⁻¹ * y⁻¹ := by group
      _ = x * y * (x⁻¹ * w) * w⁻¹ * y⁻¹ := by rw [h2 x⁻¹]
      _ = x * y * x⁻¹ * y⁻¹ := by group
  have hcm1 : ∀ x x' y : G, ⁅x * x', y⁆ = x * ⁅x', y⁆ * x⁻¹ * ⁅x, y⁆ := by
    intro x x' y
    simp only [commutatorElement_def]
    group
  have hcm2 : ∀ x y y' : G, ⁅x, y * y'⁆ = ⁅x, y⁆ * (y * ⁅x, y'⁆ * y⁻¹) := by
    intro x y y'
    simp only [commutatorElement_def]
    group
  have hcm3 : ∀ m x y : G, ⁅m⁻¹ * x * m, m⁻¹ * y * m⁆ = m⁻¹ * ⁅x, y⁆ * m := by
    intro m x y
    simp only [commutatorElement_def]
    group
  let β : G ⧸ Subgroup.center G → G ⧸ Subgroup.center G → ZMod 2 :=
    fun u v => ψ ⁅Quotient.out u, Quotient.out v⁆
  have hβ : ∀ x y : G, β (QuotientGroup.mk' (Subgroup.center G) x)
      (QuotientGroup.mk' (Subgroup.center G) y) = ψ ⁅x, y⁆ := by
    intro x y
    obtain ⟨z, hz⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center G) x
    obtain ⟨w, hw⟩ := QuotientGroup.mk_out_eq_mul (Subgroup.center G) y
    show ψ ⁅Quotient.out (QuotientGroup.mk' (Subgroup.center G) x),
      Quotient.out (QuotientGroup.mk' (Subgroup.center G) y)⁆ = ψ ⁅x, y⁆
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, hz, hw, hcc x y z w z.2 w.2]
  have hb1 : ∀ x ∈ (Sbar : Subgroup (G ⧸ Subgroup.center G)),
      ∀ x' ∈ (Sbar : Subgroup (G ⧸ Subgroup.center G)),
      ∀ y ∈ (Sbar : Subgroup (G ⧸ Subgroup.center G)), β (x * x') y = β x y + β x' y := by
    intro x hx x' hx' y hy
    rw [hSbar] at hx hx' hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨x', hx', rfl⟩ := hx'
    obtain ⟨y, hy, rfl⟩ := hy
    obtain ⟨hmem, hval⟩ := hconjx x hx _ (hSS (Subgroup.commutator_mem_commutator hx' hy))
    rw [← map_mul, hβ, hβ, hβ, hcm1,
      hψmul _ hmem _ (hSS (Subgroup.commutator_mem_commutator hx hy)), hval, add_comm]
  have hb2 : ∀ x ∈ (Sbar : Subgroup (G ⧸ Subgroup.center G)),
      ∀ y ∈ (Sbar : Subgroup (G ⧸ Subgroup.center G)),
      ∀ y' ∈ (Sbar : Subgroup (G ⧸ Subgroup.center G)), β x (y * y') = β x y + β x y' := by
    intro x hx y hy y' hy'
    rw [hSbar] at hx hy hy'
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    obtain ⟨y', hy', rfl⟩ := hy'
    obtain ⟨hmem, hval⟩ := hconjx y hy _ (hSS (Subgroup.commutator_mem_commutator hx hy'))
    rw [← map_mul, hβ, hβ, hβ, hcm2,
      hψmul _ (hSS (Subgroup.commutator_mem_commutator hx hy)) _ hmem, hval]
  have hb3 : ∀ z ∈ sylowCenter (Sbar : Subgroup (G ⧸ Subgroup.center G)),
      ∀ y ∈ (Sbar : Subgroup (G ⧸ Subgroup.center G)), β z y = 0 := by
    intro z hz y hy
    rw [← hOmZ, hΩ] at hz
    rw [hSbar] at hy
    obtain ⟨a, ha, rfl⟩ := hz
    obtain ⟨y, hy, rfl⟩ := hy
    rw [hβ]
    apply hψA
    have h := hconjS y⁻¹ ((S : Subgroup G).inv_mem hy) a⁻¹ (A.inv_mem ha)
    rw [inv_inv] at h
    have he : ⁅a, y⁆ = a * (y * a⁻¹ * y⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [he]
    exact A.mul_mem ha h
  have hb4 : ∀ x ∈ (Sbar : Subgroup (G ⧸ Subgroup.center G)),
      ∀ z ∈ sylowCenter (Sbar : Subgroup (G ⧸ Subgroup.center G)), β x z = 0 := by
    intro x hx z hz
    rw [← hOmZ, hΩ] at hz
    rw [hSbar] at hx
    obtain ⟨a, ha, rfl⟩ := hz
    obtain ⟨x, hx, rfl⟩ := hx
    rw [hβ]
    apply hψA
    have h := hconjS x⁻¹ ((S : Subgroup G).inv_mem hx) a ha
    rw [inv_inv] at h
    rw [commutatorElement_def]
    exact A.mul_mem h (A.inv_mem ha)
  have hb5 : ∀ n ∈ Subgroup.normalizer
      ((Sbar : Subgroup (G ⧸ Subgroup.center G)) : Set (G ⧸ Subgroup.center G)),
      ∀ x ∈ (Sbar : Subgroup (G ⧸ Subgroup.center G)),
      ∀ y ∈ (Sbar : Subgroup (G ⧸ Subgroup.center G)),
      β (n⁻¹ * x * n) (n⁻¹ * y * n) = β x y := by
    intro n hn x hx y hy
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) n
    have hmS : m ∈ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
      have h := Subgroup.le_normalizer_comap (QuotientGroup.mk' (Subgroup.center G))
        (H := (Sbar : Subgroup (G ⧸ Subgroup.center G))) hn
      rwa [hSbar, hSc] at h
    have hmA : ∀ a ∈ A, m⁻¹ * a * m ∈ A := fun a ha =>
      hA.closed a ha m ((Subgroup.mem_normalizer_iff''.mp hmS a).mp (hA.le ha))
    rw [hSbar] at hx hy
    obtain ⟨x, hx, rfl⟩ := hx
    obtain ⟨y, hy, rfl⟩ := hy
    rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul, hβ, hβ, hcm3,
      (hψconj m hmA _ (hSS (Subgroup.commutator_mem_commutator hx hy))).2]
  have hzero := h13 (G ⧸ Subgroup.center G) hB Sbar β hb1 hb2 hb3 hb4 hb5
  have hSSM : ⁅(S : Subgroup G), (S : Subgroup G)⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have h := hzero (QuotientGroup.mk' (Subgroup.center G) x)
      (by rw [hSbar]; exact Subgroup.mem_map_of_mem _ hx)
      (QuotientGroup.mk' (Subgroup.center G) y)
      (by rw [hSbar]; exact Subgroup.mem_map_of_mem _ hy)
    rw [hβ] at h
    by_contra hM
    have h1 : ψ ⁅x, y⁆ = 1 := ite_eq_right hM
    rw [h1] at h
    exact one_ne_zero h
  have hZSS : Subgroup.center G ≤ ⁅(S : Subgroup G), (S : Subgroup G)⁆ := fun z hz =>
    mem_commutator_of_mem_center S hq.1 hz (hZS hz)
  have hle : A ⊔ Subgroup.center G ≤ M := sup_le hAM (hZSS.trans hSSM)
  rw [Subgroup.subgroupOf_eq_top.mpr hle, Subgroup.index_top] at hM2
  exact absurd hM2 (by norm_num)

theorem N28_of (h11b : S_N11b) : S_N28 := by
  intro G _ _ S A hA hq htype hAbar hZA
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2
  have hZS : Subgroup.center G ≤ (S : Subgroup G) :=
    (isPGroup_center_of_oddCore hA.oddCore).le_sylow_of_normal S
  let Sbar : Sylow 2 (G ⧸ Subgroup.center G) :=
    S.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center G))
  have hSbar : (Sbar : Subgroup (G ⧸ Subgroup.center G)) =
      (S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G)) :=
    Sylow.coe_mapSurjective _ _
  have hΩ : Omega1 (Sbar : Subgroup (G ⧸ Subgroup.center G)) =
      A.map (QuotientGroup.mk' (Subgroup.center G)) := by
    rw [hSbar, hAbar]
  have hOm : IsMulCommutative (Omega1 (Sbar : Subgroup (G ⧸ Subgroup.center G))) := by
    rw [hΩ]
    exact isMulCommutative_map hA.comm _
  obtain ⟨h4, htrans⟩ := h11b (G ⧸ Subgroup.center G) htype Sbar hOm
  have hcomap : (A.map (QuotientGroup.mk' (Subgroup.center G))).comap
      (QuotientGroup.mk' (Subgroup.center G)) = A := by
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hZA]
  have hsq : ∀ u ∈ A.map (QuotientGroup.mk' (Subgroup.center G)), u ^ 2 = 1 := fun u hu =>
    sq_eq_one_of_mem_omega1 hOm (hΩ ▸ hu)
  have ha2 : ∀ a ∈ A, a ^ 2 ∈ Subgroup.center G := by
    intro a ha
    have h := hsq _ (Subgroup.mem_map_of_mem (QuotientGroup.mk' (Subgroup.center G)) ha)
    rwa [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
  have hconj2 : ∀ a ∈ A, ∀ m : G, (m⁻¹ * a * m) ^ 2 = a ^ 2 := by
    intro a ha m
    have h := Subgroup.mem_center_iff.mp (ha2 a ha) m
    calc (m⁻¹ * a * m) ^ 2 = m⁻¹ * (a ^ 2 * m) := by simp only [sq]; group
      _ = m⁻¹ * (m * a ^ 2) := by rw [h]
      _ = a ^ 2 := inv_mul_cancel_left m _
  have hsqc : ∀ g z : G, z ∈ Subgroup.center G → (g * z) ^ 2 = g ^ 2 * z ^ 2 := by
    intro g z hz
    have h := Subgroup.mem_center_iff.mp hz g
    calc (g * z) ^ 2 = g * (z * g) * z := by simp only [sq]; group
      _ = g * (g * z) * z := by rw [h]
      _ = g ^ 2 * z ^ 2 := by simp only [sq]; group
  have hP : ∀ a ∈ A, ∃ z ∈ Subgroup.center G, a ^ 2 = z ^ 2 := by
    intro a ha
    by_cases ha1 : QuotientGroup.mk' (Subgroup.center G) a = 1
    · refine ⟨a, ?_, rfl⟩
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at ha1
    obtain ⟨b, hb, hb1, hba⟩ : ∃ b ∈ A, QuotientGroup.mk' (Subgroup.center G) b ≠ 1 ∧
        QuotientGroup.mk' (Subgroup.center G) b ≠ QuotientGroup.mk' (Subgroup.center G) a := by
      by_contra hno
      push Not at hno
      have hsub : ((A.map (QuotientGroup.mk' (Subgroup.center G)) :
          Subgroup (G ⧸ Subgroup.center G)) : Set (G ⧸ Subgroup.center G)) ⊆
          {1, QuotientGroup.mk' (Subgroup.center G) a} := by
        rintro _ ⟨b, hb, rfl⟩
        by_cases hb1 : QuotientGroup.mk' (Subgroup.center G) b = 1
        · exact Or.inl hb1
        · exact Or.inr (hno b hb hb1)
      have hle : Nat.card (A.map (QuotientGroup.mk' (Subgroup.center G))) ≤ 2 := by
        rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
        exact (Set.ncard_le_ncard hsub).trans ((Set.ncard_insert_le _ _).trans (by simp))
      rw [← hΩ] at hle
      omega
    have hπa : QuotientGroup.mk' (Subgroup.center G) a ∈
        Omega1 (Sbar : Subgroup (G ⧸ Subgroup.center G)) :=
      hΩ ▸ Subgroup.mem_map_of_mem _ ha
    have hπb : QuotientGroup.mk' (Subgroup.center G) b ∈
        Omega1 (Sbar : Subgroup (G ⧸ Subgroup.center G)) :=
      hΩ ▸ Subgroup.mem_map_of_mem _ hb
    have hab1 : QuotientGroup.mk' (Subgroup.center G) a *
        QuotientGroup.mk' (Subgroup.center G) b ≠ 1 := by
      intro h
      apply hba
      have h2 : QuotientGroup.mk' (Subgroup.center G) a *
          QuotientGroup.mk' (Subgroup.center G) a = 1 := by
        rw [← sq]
        exact hsq _ (Subgroup.mem_map_of_mem _ ha)
      calc QuotientGroup.mk' (Subgroup.center G) b
          = (QuotientGroup.mk' (Subgroup.center G) a *
              QuotientGroup.mk' (Subgroup.center G) a) *
              QuotientGroup.mk' (Subgroup.center G) b := by rw [h2, one_mul]
        _ = QuotientGroup.mk' (Subgroup.center G) a *
              (QuotientGroup.mk' (Subgroup.center G) a *
                QuotientGroup.mk' (Subgroup.center G) b) := by rw [mul_assoc]
        _ = QuotientGroup.mk' (Subgroup.center G) a := by rw [h, mul_one]
    obtain ⟨n₁, -, hn₁⟩ := htrans _ hπa _ hπb ha1 hb1
    obtain ⟨n₂, -, hn₂⟩ := htrans _ hπa _ (Subgroup.mul_mem _ hπa hπb) ha1 hab1
    obtain ⟨m₁, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) n₁
    obtain ⟨m₂, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center G) n₂
    rw [← map_inv, ← map_mul, ← map_mul] at hn₁ hn₂
    rw [← map_mul] at hn₂
    obtain ⟨z₁, hz₁, he₁⟩ : ∃ z₁ ∈ Subgroup.center G, m₁⁻¹ * a * m₁ = b * z₁ := by
      refine ⟨b⁻¹ * (m₁⁻¹ * a * m₁), ?_, by group⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hn₁
      exact QuotientGroup.eq.mp hn₁.symm
    obtain ⟨w₁, hw₁, he₂⟩ : ∃ w₁ ∈ Subgroup.center G, m₂⁻¹ * a * m₂ = a * b * w₁ := by
      refine ⟨(a * b)⁻¹ * (m₂⁻¹ * a * m₂), ?_, by group⟩
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply] at hn₂
      exact QuotientGroup.eq.mp hn₂.symm
    have hab : a * b = b * a := congrArg Subtype.val (hA.comm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hab2 : (a * b) ^ 2 = a ^ 2 * b ^ 2 := by
      calc (a * b) ^ 2 = a * (b * a) * b := by simp only [sq]; group
        _ = a * (a * b) * b := by rw [hab]
        _ = a ^ 2 * b ^ 2 := by simp only [sq]; group
    have k₁ : a ^ 2 = b ^ 2 * z₁ ^ 2 := by
      rw [← hconj2 a ha m₁, he₁, hsqc b z₁ hz₁]
    have k₂ : a ^ 2 = a ^ 2 * (b ^ 2 * w₁ ^ 2) := by
      rw [← mul_assoc, ← hab2, ← hsqc (a * b) w₁ hw₁, ← he₂, hconj2 a ha m₂]
    have k₃ : b ^ 2 * w₁ ^ 2 = 1 := mul_left_cancel (k₂.symm.trans (mul_one _).symm)
    refine ⟨w₁⁻¹ * z₁, Subgroup.mul_mem _ (Subgroup.inv_mem _ hw₁) hz₁, ?_⟩
    rw [hsqc _ _ hz₁, inv_pow, ← eq_inv_of_mul_eq_one_left k₃]
    exact k₁
  rw [coreConclusion_iff hq hA.oddCore S A]
  refine ⟨htype, le_antisymm ?_ (sup_le hZA ?_)⟩
  ·
    intro a ha
    obtain ⟨z, hz, h⟩ := hP a ha
    have hzi : z⁻¹ ∈ Subgroup.center G := Subgroup.inv_mem _ hz
    have ht : z⁻¹ * a ∈ Omega1 (S : Subgroup G) := by
      apply Subgroup.subset_closure
      refine ⟨(S : Subgroup G).mul_mem (hZS hzi) (hA.le ha), ?_⟩
      rw [(Subgroup.mem_center_iff.mp hzi a).symm, hsqc a z⁻¹ hzi, h, inv_pow, mul_inv_cancel]
    have hmem := Subgroup.mul_mem_sup hz ht
    rwa [mul_inv_cancel_left] at hmem
  ·
    rw [Omega1, Subgroup.closure_le]
    rintro t ⟨htS, ht2⟩
    have h1 : QuotientGroup.mk' (Subgroup.center G) t ∈
        Omega1 ((S : Subgroup G).map (QuotientGroup.mk' (Subgroup.center G))) :=
      Subgroup.subset_closure ⟨Subgroup.mem_map_of_mem _ htS, by rw [← map_pow, ht2, map_one]⟩
    rw [← hAbar] at h1
    rw [SetLike.mem_coe, ← hcomap]
    exact h1

end CFSG.Goldschmidt
