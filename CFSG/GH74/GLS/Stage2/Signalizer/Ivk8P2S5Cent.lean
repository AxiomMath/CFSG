module

public import CFSG.GH74.GLS.Stage2.Signalizer.Ivk8P2S5Comm
public import CFSG.GH74.GLS.Stage2.Bender.Thm2.L915Lem96

public section

namespace CFSG.GH74.GLS.Stage2.Signalizer.Ivk8

open Subgroup CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.Blueprint CFSG.Assembly.LowTwoRank
  CFSG.GH74.GLS.Stage12 CFSG.GH74.GLS.Stage2.Local CFSG.GH74.GLS.Bg
  CFSG.GH74.GLS.Stage2.Final.Thm4 CFSG.GH74.GLS.Stage2.Bender.Thm1
  CFSG.GH74.GLS.Stage2.Bender.Thm2
open scoped commutatorElement

section Cent

variable {G : Type} [Group G]

theorem z_mem_normalizer_of_comm [Finite G] {Y : Subgroup G} {z : G} (h : ⁅Y, zpowers z⁆ = Y) :
    z ∈ normalizer (Y : Set G) := by
  have := le_normalizer_commutator (H := zpowers z) (K := Y) (Subgroup.mem_zpowers z)
  rwa [Subgroup.commutator_comm, h] at this

theorem mul_self_eq_one_of_orderOf {z : G} (h : orderOf z = 2) : z * z = 1 := by
  have : z ^ 2 = 1 := orderOf_dvd_iff_pow_eq_one.1 (dvd_of_eq h)
  simpa [pow_two] using this

theorem commutator_zpowers_le_of {H K : Subgroup G} {z : G} (hz2 : z * z = 1)
    (h : ∀ c ∈ H, ⁅c, z⁆ ∈ K) : ⁅H, zpowers z⁆ ≤ K := by
  refine Subgroup.commutator_le.2 fun c hc y hy => ?_
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rcases zpow_one_or_self_of_mul_self hz2 n with h1 | h1
  · rw [h1]
    simp
  · rw [h1]
    exact h c hc

theorem ne_bot_of_isCompIn {H J : Subgroup G} (hJ : IsCompIn H J) : J ≠ ⊥ := by
  have hq : CFSG.IsQuasisimple ↥J :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ.1) hJ.2.1
  have : Nontrivial ↥J := CFSG.LocalCores.isQuasisimple_nontrivial hq
  exact (Subgroup.nontrivial_iff_ne_bot J).1 this

theorem card_le_mul_card_inf [Finite G] {J Z K D : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hZ : Z ≤ normalizer (J : Set G)) (hK : K ≤ centralizer (J : Set G))
    (hD : D ≤ Z ⊔ K) (hidx : (centralizer (J : Set G) ⊓ Z).relIndex Z = p) :
    Nat.card ↥D ≤ p * Nat.card ↥(D ⊓ centralizer (J : Set G)) := by
  classical
  have hCA : centralizer (J : Set G) ≤ normalizer (J : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hKA : K ≤ normalizer (J : Set G) := hK.trans hCA
  have hDA : D ≤ normalizer (J : Set G) := hD.trans (sup_le hZ hKA)
  let π := J.normalizerMonoidHom
  have hker : π.ker = (centralizer (J : Set G)).subgroupOf (normalizer (J : Set G)) :=
    Subgroup.normalizerMonoidHom_ker J
  have hKker : K.subgroupOf (normalizer (J : Set G)) ≤ π.ker := by
    rw [hker]
    intro x hx
    exact hK hx
  have hsup : (Z ⊔ K).subgroupOf (normalizer (J : Set G)) =
      Z.subgroupOf (normalizer (J : Set G)) ⊔ K.subgroupOf (normalizer (J : Set G)) :=
    Subgroup.subgroupOf_sup hZ hKA
  have hmap : (D.subgroupOf (normalizer (J : Set G))).map π ≤
      (Z.subgroupOf (normalizer (J : Set G))).map π := by
    have h1 : D.subgroupOf (normalizer (J : Set G)) ≤
        (Z ⊔ K).subgroupOf (normalizer (J : Set G)) := fun x hx => hD hx
    calc (D.subgroupOf (normalizer (J : Set G))).map π
        ≤ ((Z ⊔ K).subgroupOf (normalizer (J : Set G))).map π := Subgroup.map_mono h1
      _ = (Z.subgroupOf (normalizer (J : Set G))).map π ⊔
            (K.subgroupOf (normalizer (J : Set G))).map π := by rw [hsup, Subgroup.map_sup]
      _ = (Z.subgroupOf (normalizer (J : Set G))).map π := by
        rw [(Subgroup.map_eq_bot_iff _).2 hKker, sup_bot_eq]
  have hZcard : Nat.card ↥((Z.subgroupOf (normalizer (J : Set G))).map π) = p := by
    rw [← Subgroup.relIndex_ker, hker, Subgroup.relIndex_subgroupOf hZ,
      ← Subgroup.inf_relIndex_right]
    exact hidx
  have hdvd : Nat.card ↥((D.subgroupOf (normalizer (J : Set G))).map π) ∣ p := by
    rw [← hZcard]
    exact Subgroup.card_dvd_of_le hmap
  have hD'card : Nat.card ↥(D.subgroupOf (normalizer (J : Set G))) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDA).toEquiv
  have hmul := Subgroup.relIndex_mul_card π.ker (D.subgroupOf (normalizer (J : Set G)))
  rw [Subgroup.relIndex_ker] at hmul
  have hle : Nat.card ↥((D.subgroupOf (normalizer (J : Set G))).map π) ≤ p :=
    Nat.le_of_dvd hp.pos hdvd
  have hkerD : Nat.card ↥(π.ker ⊓ D.subgroupOf (normalizer (J : Set G))) =
      Nat.card ↥(D ⊓ centralizer (J : Set G)) := by
    have h1 : π.ker ⊓ D.subgroupOf (normalizer (J : Set G)) =
        (D ⊓ centralizer (J : Set G)).subgroupOf (normalizer (J : Set G)) := by
      ext x
      simp only [hker, Subgroup.mem_inf, Subgroup.mem_subgroupOf]
      exact and_comm
    rw [h1]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hDA)).toEquiv
  calc Nat.card ↥D = Nat.card ↥(D.subgroupOf (normalizer (J : Set G))) := hD'card.symm
    _ = Nat.card ↥((D.subgroupOf (normalizer (J : Set G))).map π) *
          Nat.card ↥(π.ker ⊓ D.subgroupOf (normalizer (J : Set G))) := hmul.symm
    _ ≤ p * Nat.card ↥(π.ker ⊓ D.subgroupOf (normalizer (J : Set G))) :=
        Nat.mul_le_mul_right _ hle
    _ = p * Nat.card ↥(D ⊓ centralizer (J : Set G)) := by rw [hkerD]

theorem exists_centralizing_of_relIndex [Finite G] {J Z K D : Subgroup G} {p : ℕ}
    (hp : p.Prime) (hZ : Z ≤ normalizer (J : Set G)) (hK : K ≤ centralizer (J : Set G))
    (hD : D ≤ Z ⊔ K) (hDc : Nat.card ↥D = p ^ 2)
    (hidx : (centralizer (J : Set G) ⊓ Z).relIndex Z = p) :
    ∃ d ∈ D, d ≠ 1 ∧ d ∈ centralizer (J : Set G) := by
  have h := card_le_mul_card_inf hp hZ hK hD hidx
  rw [hDc] at h
  by_contra hcon
  push Not at hcon
  have hbot : D ⊓ centralizer (J : Set G) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    exact hcon x hx.1 (fun h1 => hx1 (Subgroup.mem_bot.2 h1)) hx.2
  rw [hbot, Subgroup.card_bot, mul_one] at h
  have := hp.two_le
  nlinarith

theorem commutator_zpowers_eq_bot_of_le {H : Subgroup G} {z : G}
    (h : H ≤ centralizer ({z} : Set G)) : ⁅H, zpowers z⁆ = ⊥ := by
  rw [eq_bot_iff]
  refine Subgroup.commutator_le.2 fun x hx y hy => ?_
  have hc : Commute x z := Subgroup.mem_centralizer_singleton_iff.1 (h hx)
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  exact Subgroup.mem_bot.2 ((commutatorElement_eq_one_iff_commute).2 (hc.zpow_right n))

theorem not_le_of_mem_XfamR {z : G} {M V Y : Subgroup G} (hMz : M = centralizer {z})
    (hY : Y ∈ XfamR z M V) : ¬ Y ≤ M := by
  intro hYM
  apply hY.1
  rw [← hY.2.2.2.1]
  exact commutator_zpowers_eq_bot_of_le (hMz ▸ hYM)

end Cent

section FpiInv

variable {G : Type} [Group G] [Finite G]

theorem inverts_F1 {z : G} {M Y : Subgroup G} (hMz : M = centralizer {z}) (hz2' : z * z = 1)
    (hzY : z ∈ normalizer (Y : Set G)) (hF1 : Fpi (piF' M) Y ⊓ M = ⊥) :
    (∀ f ∈ Fpi (piF' M) Y, z * f * z⁻¹ = f⁻¹) ∧ ∀ f ∈ Fpi (piF' M) Y, Odd (orderOf f) := by
  have hzF : z ∈ normalizer ((Fpi (piF' M) Y : Subgroup G) : Set G) := by
    refine mem_normalizer_of_cj_eq ?_
    have h := Fpi_cj (piF' M) z Y
    rw [cj_eq_of_mem_normalizer hzY] at h
    exact h.symm
  have hfpf : ∀ f ∈ Fpi (piF' M) Y, z * f = f * z → f = 1 := by
    intro f hf hcomm
    have hfz : f ∈ centralizer ({z} : Set G) :=
      Subgroup.mem_centralizer_singleton_iff.2 hcomm.symm
    exact Subgroup.mem_bot.1 (hF1 ▸ (⟨hf, hMz ▸ hfz⟩ : f ∈ Fpi (piF' M) Y ⊓ M))
  have hinv : ∀ f ∈ Fpi (piF' M) Y, z * f * z⁻¹ = f⁻¹ := inverts_of_fixed_free hz2' hzF hfpf
  exact ⟨hinv, fun f hf => odd_orderOf_of_fpf hinv hfpf hf⟩

end FpiInv


section NatSec

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem cj_sup (b : G) (A B : Subgroup G) : cj b (A ⊔ B) = cj b A ⊔ cj b B :=
  Subgroup.map_sup _ _ _

theorem Em_cj (b : G) (X : Subgroup G) : Em (cj b X) = cj b (Em X) :=
  CFSG.GH74.GLS.Stage2.Bender.Thm1.BenderProof.Em_map (MulAut.conj b) X

theorem le_normalizer_Em (X : Subgroup G) : X ≤ normalizer ((Em X : Subgroup G) : Set G) :=
  fun g hg => by
    refine mem_normalizer_of_cj_eq ?_
    rw [← Em_cj, cj_self_of_mem hg]

omit [Finite G] in
theorem mem_normalizer_sup {b : G} {A B : Subgroup G} (hA : b ∈ normalizer (A : Set G))
    (hB : b ∈ normalizer (B : Set G)) : b ∈ normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  refine mem_normalizer_of_cj_eq ?_
  rw [cj_sup, cj_eq_of_mem_normalizer hA, cj_eq_of_mem_normalizer hB]

theorem cj_XdR (M : Subgroup G) (a d : G) : cj a (XdR M d) = XdR M (a * d * a⁻¹) := by
  unfold XdR
  rw [cj_sup, ← Em_cj, ← Fpi_cj, cj_centralizer]

end NatSec

section FpiSub

variable {G : Type} [Group G] [Finite G]

theorem Op_le_Fpi {σ : Set ℕ} {q : ℕ} (hq : q ∈ σ) (hqp : q.Prime) (N : Subgroup G) :
    Op q N ≤ Fpi σ N := by
  have : Op q N = Op q (Fm N) := (Op_Fm_eq hqp N).symm
  rw [this]
  exact le_iSup₂_of_le q hq le_rfl

theorem Fpi_le_iSup_Op {σ : Set ℕ} (hσ : ∀ q ∈ σ, q.Prime) (N : Subgroup G) :
    Fpi σ N ≤ ⨆ q ∈ σ, Op q N := by
  refine iSup₂_le fun q hq => ?_
  rw [Op_Fm_eq (hσ q hq) N]
  exact le_iSup₂_of_le q hq le_rfl

theorem not_dvd_card_of_le_Fpi {σ : Set ℕ} (hσ : ∀ q ∈ σ, q.Prime) {p : ℕ} (hp : p.Prime)
    (hpσ : p ∉ σ) (N : Subgroup G) {X : Subgroup G} (hX : X ≤ Fpi σ N) :
    ¬ p ∣ Nat.card ↥X := by
  have : Fact p.Prime := ⟨hp⟩
  have hle : Fpi σ N ≤ pPrimeCoreOf p (Fm N) := by
    refine iSup₂_le fun q hq => ?_
    have hqp : q ≠ p := fun h => hpσ (h ▸ hq)
    exact L915.Op_le_pPrimeCoreOf (hσ q hq) hp hqp (Fm N)
  have hcop : Nat.Coprime p (Nat.card ↥(pPrimeCoreOf p (Fm N))) := by
    rw [pPrimeCoreOf, Subgroup.card_map_of_injective (Fm N).subtype_injective]
    exact CFSG.pPrimeCore_coprime_card
  intro hdvd
  have h2 : p ∣ Nat.card ↥(pPrimeCoreOf p (Fm N)) :=
    hdvd.trans (Subgroup.card_dvd_of_le (hX.trans hle))
  have h3 : p ∣ Nat.gcd p (Nat.card ↥(pPrimeCoreOf p (Fm N))) := Nat.dvd_gcd (dvd_refl p) h2
  rw [hcop.gcd_eq_one] at h3
  exact hp.one_lt.ne' (Nat.dvd_one.1 h3)

end FpiSub

end CFSG.GH74.GLS.Stage2.Signalizer.Ivk8
