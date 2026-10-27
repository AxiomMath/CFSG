module

public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndLift
public import CFSG.LocalAnalysis.ComponentClassification.HarrisEndSetting

public noncomputable section

namespace CFSG.ComponentClassification.HarrisLit

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer CFSG.ABGLocalTools HarrisEnd
open Standing.Setup42

theorem EndB.exists_mem_inf_center {G : Type*} [Group G] [Finite G] {P N : Subgroup G}
    (hP : IsPGroup 2 P) (hNP : N ≤ P) (hNn : ∀ g ∈ P, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hN : N ≠ ⊥) :
    ∃ y ∈ N, y ≠ 1 ∧ ∀ g ∈ P, g * y = y * g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent P := hP.isNilpotent
  set N' := N.subgroupOf P with hN'
  have hN'n : N'.Normal := ⟨fun n hn g => by
    rw [hN', mem_subgroupOf] at hn ⊢
    exact hNn g g.2 n hn⟩
  have hN'ne : N' ≠ ⊥ := by
    intro h
    apply hN
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hNP hx⟩ : P) ∈ N' := hx
    rw [h, mem_bot] at this
    exact mem_bot.mpr (congrArg Subtype.val this)
  have := Group.IsNilpotent.inf_center_ne_bot_of_normal hN'ne
  obtain ⟨⟨y, hy⟩, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp this
  obtain ⟨hyN, hyZ⟩ := mem_inf.mp hy
  refine ⟨(y : G), hyN, fun h => hy1 (Subtype.ext (Subtype.ext h)), fun g hg => ?_⟩
  have := mem_center_iff.mp hyZ ⟨g, hg⟩
  exact congrArg Subtype.val this

theorem EndB.card_inf_le_of_card_le {G : Type*} [Group G] [Finite G] {W U K : Subgroup G}
    (hWU : W ≤ U) {m : ℕ} (hm : Nat.card U ≤ m * Nat.card W) :
    Nat.card ↥(U ⊓ K) ≤ m * Nat.card ↥(W ⊓ K) := by
  have h1 := Subgroup.relIndex_mul_card W (U ⊓ K)
  have h2 := Subgroup.relIndex_mul_card W U
  rw [inf_of_le_left hWU] at h2
  have hpos : 0 < Nat.card W := Nat.card_pos
  have hne : W.relIndex U ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := U)).ne' h2.symm
  have hrel : W.relIndex (U ⊓ K) ≤ W.relIndex U :=
    Subgroup.relIndex_le_of_le_right inf_le_left hne
  have hle : W.relIndex U ≤ m := by
    by_contra hlt
    have : (m + 1) * Nat.card W ≤ W.relIndex U * Nat.card W :=
      Nat.mul_le_mul_right _ (by omega)
    nlinarith
  have hWK : W ⊓ (U ⊓ K) = W ⊓ K := by
    rw [← inf_assoc, inf_of_le_left hWU]
  rw [hWK] at h1
  rw [← h1]
  exact Nat.mul_le_mul_right _ (hrel.trans hle)

variable {X : Type} [Group X] [Finite X] {t : X} {L : Subgroup X} {p f : ℕ} {S : Subgroup X}
  {w z : X} {V : Subgroup X} {i j : ℕ}

namespace Setting46e

theorem z_mem_center_W (hKC : AutPSL2CentralizerInput) (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))] {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    z ∈ W ⊓ centralizer (W : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set β := w ^ (orderOf w / 2) * t ^ i * z ^ j with hβ
  set M := centralizer ({β} : Set X) with hM
  set E := layer (MBar β) with hE
  obtain ⟨hβZ, hZle⟩ := Standing.Setup42.center_W hKC hs.setup hs.sylow_V hs.le_V hs.beta hW hUW
  have hWM : W ≤ M := hW.le
  have hW2 := hW.isPGroup
  have hβ2 : β ^ 2 = 1 := hs.setup.sq_eq_one_of_mem_X (beta_mem_X i j)
  have hz2 : z ^ 2 = 1 := by rw [← hs.setup.z_order]; exact pow_orderOf_eq_one z
  have hzK : z ∈ centralizerResidual L β := hs.lemma45.z_mem.2
  have hzM : z ∈ M := K_le_centralizer_beta i j hzK
  have hβz : β * z = z * β := (mem_centralizer_singleton_iff.mp hzM).symm
  have hTW : zpowers t ⊔ (S ⊓ L) ⊔ zpowers w ≤ W := hs.beta.lt.le.trans hUW
  have hzW : z ∈ W := hTW (mem_sup_left (mem_sup_right hs.setup.z_mem))
  have hz1 : z ≠ 1 := by
    intro h
    have := hs.setup.z_order
    rw [h, orderOf_one] at this
    norm_num at this
  have hEn : E.Normal := inferInstance
  have hKnab := nonabelian_of_lieModel_psl2 (hs.lieModel_KBar h412)
  have hCE := centralizer_inf_layer_eq_bot hs.KBar_le_layer hKnab
  have hbE : ∀ y ∈ E, y ∈ centralizer (E : Set (MBar β)) → y = 1 := fun y hy hyC => by
    have : y ∈ centralizer (E : Set (MBar β)) ⊓ E := ⟨hyC, hy⟩
    rwa [hCE, mem_bot] at this
  have hβC : betaBar β ∈ centralizer (E : Set (MBar β)) :=
    mem_centralizer_iff.mpr fun h _ => mem_center_iff.mp (betaBar_mem_center β) h
  have hzE : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) ∈ E := hs.KBar_le_layer ⟨⟨z, hzM⟩, hzK, rfl⟩
  set Wb := barOf M W with hWb
  have hWb2 : IsPGroup 2 Wb := (isPGroup_subgroupOf hWM hW2).map _
  have hzWb : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) ∈ Wb ⊓ E := ⟨mk_mem_barOf hzM hzW, hzE⟩
  have hzb1 : (QuotientGroup.mk ⟨z, hzM⟩ : MBar β) ≠ 1 := fun h =>
    hz1 (mk_injOn hWM hW2 hzW (one_mem W) h)
  have hNne : Wb ⊓ E ≠ ⊥ := fun h => hzb1 (by rw [h] at hzWb; exact mem_bot.mp hzWb)
  obtain ⟨y, hyN, hy1, hyc⟩ := EndB.exists_mem_inf_center hWb2 inf_le_left
    (fun g hg n hn => mem_inf.mpr ⟨mul_mem (mul_mem hg (mem_inf.mp hn).1) (inv_mem hg),
      hEn.conj_mem n (mem_inf.mp hn).2 g⟩) hNne
  obtain ⟨y', hy'W, rfl⟩ := mem_barOf.mp (mem_inf.mp hyN).1
  have hy'Z : (y' : X) ∈ W ⊓ centralizer (W : Set X) := by
    refine mem_inf.mpr ⟨hy'W, mem_centralizer_iff.mpr fun g hg => ?_⟩
    refine mk_injOn hWM hW2 (mul_mem hg hy'W) (mul_mem hy'W hg) ?_
    have h1 := hyc _ (mk_mem_barOf (hWM hg) hg)
    change (QuotientGroup.mk (⟨g, hWM hg⟩ * y') : MBar β) = QuotientGroup.mk (y' * ⟨g, hWM hg⟩)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    exact h1
  have hy'M : (y' : X) ∈ M := y'.2
  have hmk : ∀ a (ha : a ∈ M), (QuotientGroup.mk ⟨a, ha⟩ : MBar β) =
      QuotientGroup.mk ⟨a, ha⟩ := fun _ _ => rfl
  rcases mem_closure_pair hβ2 hz2 hβz (hZle hy'Z) with h | h | h | h
  · exfalso
    apply hy1
    have : y' = 1 := Subtype.ext h
    rw [this, QuotientGroup.mk_one]
  · exfalso
    apply hy1
    have hyβ : (QuotientGroup.mk y' : MBar β) = betaBar β := by
      rw [betaBar]
      congr 1
      exact Subtype.ext h
    rw [hyβ] at hyN ⊢
    exact hbE _ (mem_inf.mp hyN).2 hβC
  · rw [← h]
    exact hy'Z
  · exfalso
    apply hy1
    have hyβ : (QuotientGroup.mk y' : MBar β) = betaBar β * QuotientGroup.mk ⟨z, hzM⟩ := by
      rw [betaBar, ← QuotientGroup.mk_mul]
      congr 1
      exact Subtype.ext h
    have hβE : betaBar β ∈ E := by
      have := mul_mem (mem_inf.mp hyN).2 (inv_mem hzE)
      rwa [hyβ, mul_inv_cancel_right] at this
    have := hbE _ hβE hβC
    exact absurd this hs.betaBar_ne_one

theorem exists_U (hKC : AutPSL2CentralizerInput) (hs : Setting46e t L p f S w z V i j)
    (h412 : IsLemma412 L p f (w ^ (orderOf w / 2) * t ^ i * z ^ j) (hs.setup.tBar i j))
    [IsSimpleGroup ↥(layer (MBar (w ^ (orderOf w / 2) * t ^ i * z ^ j)))] {W : Subgroup X}
    (hW : IsSylowOf 2 W (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)))
    (hUW : V ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) ≤ W) :
    ∃ U : Subgroup X, IsSylowOf 2 U (centralizer ({z} : Set X)) ∧ W ≤ U ∧
      U ⊓ centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X) = W ∧
      Nat.card U ≤ 4 * Nat.card W := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hzZ := hs.z_mem_center_W hKC h412 hW hUW
  have hWz : W ≤ centralizer ({z} : Set X) := fun g hg =>
    mem_centralizer_singleton_iff.mpr ((mem_centralizer_iff.mp (mem_inf.mp hzZ).2) g hg)
  obtain ⟨U, hU, hWU⟩ := exists_isSylowOf_ge hW.isPGroup hWz
  refine ⟨U, hU, hWU, ?_, ?_⟩
  · exact (hW.eq_of_le (le_inf hWU hW.le) inf_le_right (hU.isPGroup.to_le inf_le_left))
  · calc Nat.card U ≤ twoPart (⊤ : Subgroup X) := card_le_twoPart hU.isPGroup le_top
      _ ≤ 4 * twoPart (centralizer ({w ^ (orderOf w / 2) * t ^ i * z ^ j} : Set X)) :=
        hs.beta.twoPart_le
      _ = 4 * Nat.card W := by rw [hW.card_eq]

end Setting46e

end CFSG.ComponentClassification.HarrisLit
