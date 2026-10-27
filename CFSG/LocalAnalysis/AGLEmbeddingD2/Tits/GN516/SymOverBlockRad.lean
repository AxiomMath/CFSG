module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.S3AmalgamBound.FFBlockLiftBasic

public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.AGLEmbeddingD2.GN
open CFSG.AGLEmbeddingD2.Tits.S3AmalgamBound
open scoped commutatorElement

section Helpers

variable {G : Type*} [Group G]

private theorem isPGroup_two_of_sq {V : Subgroup G} (h : ∀ x ∈ V, x ^ 2 = 1) :
    IsPGroup 2 V := by
  intro g
  exact ⟨1, Subtype.ext (by simpa using h (g : G) g.2)⟩

private theorem le_normalizer_inf_of {A B N : Subgroup G}
    (hA : N ≤ Subgroup.normalizer (A : Set G)) (hB : N ≤ Subgroup.normalizer (B : Set G)) :
    N ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  exact and_congr (Subgroup.mem_normalizer_iff.mp (hA hg) x)
    (Subgroup.mem_normalizer_iff.mp (hB hg) x)

private theorem conj_mem_of_mem_normalizer {V : Subgroup G} {x v : G}
    (hx : x ∈ Subgroup.normalizer (V : Set G)) (hv : v ∈ V) : x * v * x⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp hx v).mp hv

private theorem conj_mem_centralizer_of_le {K V : Subgroup G}
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) {g x : G} (hg : g ∈ K)
    (hx : x ∈ Subgroup.centralizer (V : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro v hv
  have hw : g⁻¹ * v * g⁻¹⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (hKV (K.inv_mem hg)) v).mp hv
  have h1 := hx _ hw
  calc v * (g * x * g⁻¹) = g * (g⁻¹ * v * g⁻¹⁻¹ * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * v * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * v := by group

private theorem le_normalizer_centralizer_of_le {K V : Subgroup G}
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) :
    K ≤ Subgroup.normalizer (Subgroup.centralizer (V : Set G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact conj_mem_centralizer_of_le hKV hg
  · intro hx
    simpa [mul_assoc] using conj_mem_centralizer_of_le hKV (K.inv_mem hg) hx

private theorem radFree_exists_pow_two_odd [Finite G] (h : G) :
    ∃ a : ℕ, Odd (orderOf (h ^ 2 ^ a)) := by
  set a := (orderOf h).factorization 2 with ha
  refine ⟨a, ?_⟩
  have hmodd : Odd (orderOf h / 2 ^ a) := by
    have : ¬ 2 ∣ orderOf h / 2 ^ a := Nat.not_dvd_ordCompl Nat.prime_two (orderOf_pos h).ne'
    exact Nat.odd_iff.mpr (by omega)
  have : orderOf (h ^ 2 ^ a) = orderOf h / 2 ^ a := by
    rw [orderOf_pow' _ (by positivity)]
    have hg : Nat.gcd (orderOf h) (2 ^ a) = 2 ^ a := Nat.gcd_eq_right (Nat.ordProj_dvd _ _)
    rw [hg]
  rw [this]; exact hmodd

private def radFreeD (K Q V : Subgroup G) (hV : K ≤ Subgroup.normalizer (V : Set G)) :
    Subgroup G where
  carrier := {x | x ∈ K ∧ ∀ q ∈ Q, ⁅q, x⁆ ∈ V}
  one_mem' := by
    show (1 : G) ∈ K ∧ ∀ q ∈ Q, ⁅q, (1 : G)⁆ ∈ V
    exact ⟨K.one_mem, fun q _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxq⟩ ⟨hy, hyq⟩
    show x * y ∈ K ∧ ∀ q ∈ Q, ⁅q, x * y⁆ ∈ V
    refine ⟨K.mul_mem hx hy, fun q hq => ?_⟩
    have e : ⁅q, x * y⁆ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact V.mul_mem (hxq q hq) (conj_mem_of_mem_normalizer (hV hx) (hyq q hq))
  inv_mem' := by
    rintro x ⟨hx, hxq⟩
    show x⁻¹ ∈ K ∧ ∀ q ∈ Q, ⁅q, x⁻¹⁆ ∈ V
    refine ⟨K.inv_mem hx, fun q hq => ?_⟩
    have e : ⁅q, x⁻¹⁆ = x⁻¹ * ⁅q, x⁆⁻¹ * x := by
      simp only [commutatorElement_def]; group
    rw [e]
    have h := conj_mem_of_mem_normalizer (hV (K.inv_mem hx)) (V.inv_mem (hxq q hq))
    rwa [inv_inv] at h

private theorem mem_radFreeD {K Q V : Subgroup G} {hV : K ≤ Subgroup.normalizer (V : Set G)}
    {x : G} :
    x ∈ radFreeD K Q V hV ↔ x ∈ K ∧ ∀ q ∈ Q, ⁅q, x⁆ ∈ V := Iff.rfl

private theorem comm_pCore_le_blockU [Finite G] {K K' : Subgroup G} (hK'K : K' ≤ K)
    (hQN : pCoreOf 2 K ≤ Subgroup.normalizer (K' : Set G)) (hK' : IsShort2 K') :
    ⁅pCoreOf 2 K, K'⁆ ≤ blockU K' := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hK'Q : K' ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hK'K.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hQK' : ⁅pCoreOf 2 K, K'⁆ ≤ pCoreOf 2 K ⊓ K' :=
    le_inf (Subgroup.le_normalizer_iff_commutator_le_left.1 hK'Q)
      (Subgroup.le_normalizer_iff_commutator_le_right.1 hQN)
  have hN : K' ≤ Subgroup.normalizer ((pCoreOf 2 K ⊓ K' : Subgroup G) : Set G) :=
    le_normalizer_inf_of hK'Q Subgroup.le_normalizer
  have hI : pCoreOf 2 K ⊓ K' ≤ pCoreOf 2 K' :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hN
      (hQ2.to_le inf_le_left)
  have h1 : ⁅pCoreOf 2 K, K'⁆ ≤ pCoreOf 2 K' := hQK'.trans hI
  exact (commutator_le_commutator_commutator_of_odd hQ2 hK'Q
    (le_closure_odd_of_isShort2 hK')).trans (Subgroup.commutator_mono h1 le_rfl)

private theorem blockU_le_comm_sup_blockZ [Finite G] {K K' V : Subgroup G}
    (hK'K : K' ≤ K) (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hV2 : IsPGroup 2 V)
    (hK' : IsShort2 K') (hK'V : ¬ K' ≤ Subgroup.centralizer (V : Set G))
    (hVQ : V ≤ pCoreOf 2 K) (hQN : pCoreOf 2 K ≤ Subgroup.normalizer (K' : Set G)) :
    blockU K' ≤ ⁅V, K'⁆ ⊔ blockZ K' := by
  have hK'V' : K' ≤ Subgroup.normalizer (V : Set G) := hK'K.trans hKV
  have hN1U : ⁅V, K'⁆ ≤ blockU K' :=
    (Subgroup.commutator_mono hVQ le_rfl).trans (comm_pCore_le_blockU hK'K hQN hK')
  have hK'N1 : K' ≤ Subgroup.normalizer (⁅V, K'⁆ : Subgroup G) :=
    Subgroup.normalizer_commutator_ge_right V K'
  have hUK' : blockU K' ≤ K' :=
    Subgroup.commutator_le_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K') le_rfl
  have hZC : blockZ K' ≤ Subgroup.centralizer (K' : Set G) := inf_le_right
  have hK'Z : K' ≤ Subgroup.normalizer (blockZ K' : Set G) :=
    (Subgroup.le_centralizer_iff.1 hZC).trans (Subgroup.centralizer_le_normalizer _)
  have hW : K' ≤ Subgroup.normalizer ((⁅V, K'⁆ ⊔ blockZ K' : Subgroup G) : Set G) :=
    fun y hy => mem_normalizer_sup (hK'N1 hy) (hK'Z hy)
  rcases hK'.2.2.2.2.2 (⁅V, K'⁆ ⊔ blockZ K') le_sup_right (sup_le hN1U inf_le_left) hW with h | h
  · exfalso
    have hN1Z : ⁅V, K'⁆ ≤ blockZ K' := le_sup_left.trans h.le
    have hc : ⁅⁅V, K'⁆, K'⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hN1Z.trans hZC)
    have h3 := commutator_le_commutator_commutator_of_odd hV2 hK'V'
      (le_closure_odd_of_isShort2 hK')
    rw [hc, le_bot_iff, Subgroup.commutator_comm] at h3
    exact hK'V (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h3)
  · exact h.ge

private theorem comm_pCore_le_comm_V [Finite G] {K K' V : Subgroup G}
    (hK'K : K' ≤ K) (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hV2 : IsPGroup 2 V)
    (hK' : IsShort2 K') (hK'V : ¬ K' ≤ Subgroup.centralizer (V : Set G))
    (hVQ : V ≤ pCoreOf 2 K) (hQN : pCoreOf 2 K ≤ Subgroup.normalizer (K' : Set G)) :
    ⁅pCoreOf 2 K, K'⁆ ≤ ⁅V, K'⁆ := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 K) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hK'Q : K' ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hK'K.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hE1 := comm_pCore_le_blockU hK'K hQN hK'
  have hU := blockU_le_comm_sup_blockZ hK'K hKV hV2 hK' hK'V hVQ hQN
  have hK'N1 : K' ≤ Subgroup.normalizer (⁅V, K'⁆ : Subgroup G) :=
    Subgroup.normalizer_commutator_ge_right V K'
  have hUK' : blockU K' ≤ K' :=
    Subgroup.commutator_le_of_le (CFSG.LieType.BorelTits.pCoreOf_le 2 K') le_rfl
  have hZK' : blockZ K' ≤ K' := inf_le_left.trans hUK'
  have hZC : blockZ K' ≤ Subgroup.centralizer (K' : Set G) := inf_le_right
  have hZN : blockZ K' ≤ Subgroup.normalizer ((⁅V, K'⁆ : Subgroup G) : Set G) :=
    fun z hz => hK'N1 (hZK' hz)
  refine (commutator_le_commutator_commutator_of_odd hQ2 hK'Q
    (le_closure_odd_of_isShort2 hK')).trans ((Subgroup.commutator_mono hE1 le_rfl).trans ?_)
  rw [Subgroup.commutator_le]
  intro u hu k hk
  have hu' : u ∈ ((⁅V, K'⁆ ⊔ blockZ K' : Subgroup G) : Set G) := hU hu
  rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZN] at hu'
  obtain ⟨a, ha, z, hz, rfl⟩ := hu'
  have hzk : k * z = z * k := Subgroup.mem_centralizer_iff.1 (hZC hz) k hk
  have h1 : z * k * z⁻¹ = k := by rw [← hzk]; group
  have hmem : ⁅a, k⁆ ∈ ⁅V, K'⁆ :=
    Subgroup.le_normalizer_iff_commutator_le_left.1 hK'N1 (Subgroup.commutator_mem_commutator ha hk)
  have e : ⁅a * z, k⁆ = a * (z * k * z⁻¹) * a⁻¹ * k⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e, h1]
  exact hmem

private theorem conjClosure_le_radFreeD {K K' V : Subgroup G} (hK'K : K' ≤ K)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hQV : ⁅pCoreOf 2 K, K'⁆ ≤ V) :
    conjClosure K' K ≤ radFreeD K (pCoreOf 2 K) V hKV := by
  have hKQ : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K
  have hK'D : K' ≤ radFreeD K (pCoreOf 2 K) V hKV := fun z hz =>
    mem_radFreeD.2 ⟨hK'K hz, fun q hq => hQV (Subgroup.commutator_mem_commutator hq hz)⟩
  refine conjClosure_le fun h hh z hz => ?_
  have hzD := (mem_radFreeD.1 (hK'D hz)).2
  refine mem_radFreeD.2 ⟨K.mul_mem (K.mul_mem hh (hK'K hz)) (K.inv_mem hh), fun q hq => ?_⟩
  have hq' : h⁻¹ * q * h ∈ pCoreOf 2 K := by
    have := (Subgroup.mem_normalizer_iff.mp (hKQ (K.inv_mem hh)) q).mp hq
    simpa using this
  have e : ⁅q, h * z * h⁻¹⁆ = h * ⁅h⁻¹ * q * h, z⁆ * h⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact conj_mem_of_mem_normalizer (hKV hh) (hzD _ hq')

private theorem twoResidual_le_conjClosure [Finite G] {K K' S : Subgroup G}
    (hS : IsSylowTwoOf S K) (hK'K : K' ≤ K) (hgen : K ≤ conjClosure K' K ⊔ S) :
    twoResidual K ≤ conjClosure K' K := by
  have hEK : conjClosure K' K ≤ K := conjClosure_le fun h hh z hz =>
    K.mul_mem (K.mul_mem hh (hK'K hz)) (K.inv_mem hh)
  have hsup : S ⊔ conjClosure K' K = K :=
    le_antisymm (sup_le hS.1 hEK) (hgen.trans (sup_le le_sup_right le_sup_left))
  exact twoResidual_le_of_isTwoQuotient hEK (le_normalizer_conjClosure K' K)
    (B6.isTwoQuotient_of_sup_eq hS.2.1 (le_normalizer_conjClosure K' K) hsup)

private theorem exists_pow_two_eq_one [Finite G] {K V : Subgroup G} (hF : CharTwo K)
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) {y : G}
    (hyD : y ∈ radFreeD K (pCoreOf 2 K) V hKV) (hyC : y ∈ Subgroup.centralizer (V : Set G)) :
    ∃ k : ℕ, y ^ 2 ^ k = 1 := by
  obtain ⟨a, ha⟩ := radFree_exists_pow_two_odd y
  refine ⟨a, ?_⟩
  have hxD := (radFreeD K (pCoreOf 2 K) V hKV).pow_mem hyD (2 ^ a)
  have hxC := (Subgroup.centralizer (V : Set G)).pow_mem hyC (2 ^ a)
  have hxK : y ^ 2 ^ a ∈ K := (mem_radFreeD.1 hxD).1
  set x := y ^ 2 ^ a with hx
  have hXD : Subgroup.zpowers x ≤ radFreeD K (pCoreOf 2 K) V hKV := Subgroup.zpowers_le.2 hxD
  have hXK : Subgroup.zpowers x ≤ K := Subgroup.zpowers_le.2 hxK
  have hXN : Subgroup.zpowers x ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hXK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
  have hXodd : Subgroup.zpowers x ≤
      Subgroup.closure {z : G | z ∈ Subgroup.zpowers x ∧ Odd (orderOf z)} :=
    Subgroup.zpowers_le.2 (Subgroup.subset_closure
      (show x ∈ {z : G | z ∈ Subgroup.zpowers x ∧ Odd (orderOf z)} from
        ⟨Subgroup.mem_zpowers x, ha⟩))
  have hXC : Subgroup.zpowers x ≤ Subgroup.centralizer (V : Set G) :=
    Subgroup.zpowers_le.2 hxC
  have hQXV : ⁅pCoreOf 2 K, Subgroup.zpowers x⁆ ≤ V :=
    Subgroup.commutator_le.2 fun q hq z hz => (mem_radFreeD.1 (hXD hz)).2 q hq
  have hVX : ⁅V, Subgroup.zpowers x⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hXC
  have hcop := commutator_le_commutator_commutator_of_odd
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) hXN hXodd
  have hbot : ⁅pCoreOf 2 K, Subgroup.zpowers x⁆ ≤ ⊥ :=
    hcop.trans ((Subgroup.commutator_mono hQXV le_rfl).trans hVX.le)
  have hXQ : Subgroup.zpowers x ≤ Subgroup.centralizer (pCoreOf 2 K : Set G) := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.1 ?_
    rw [Subgroup.commutator_comm, eq_bot_iff]
    exact hbot
  have hxQ : x ∈ pCoreOf 2 K :=
    hF (Subgroup.mem_inf.2 ⟨hxK, hXQ (Subgroup.mem_zpowers x)⟩)
  obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨x, hxQ⟩
  have hxk : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hdvd : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hxk
  have hcopr : Nat.Coprime (orderOf x) (2 ^ k) :=
    Nat.Coprime.pow_right k (Nat.coprime_two_right.2 ha)
  exact orderOf_eq_one_iff.1 (Nat.eq_one_of_dvd_coprimes hcopr dvd_rfl hdvd)

end Helpers

theorem radFree_of_shortBlock {G : Type} [Group G] [Finite G] {K S V K' : Subgroup G}
    (hS : IsSylowTwoOf S K) (hF : CharTwo K) (hred : IsTwoReducedIn K V)
    (hK'K : K' ≤ K) (hK' : IsShort2 K')
    (hQN : pCoreOf 2 K ≤ Subgroup.normalizer (K' : Set G))
    (hK'V : ¬ K' ≤ Subgroup.centralizer (V : Set G))
    (hgen : K ≤ conjClosure K' K ⊔ S) :
    twoResidual K ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K := by
  have hVK : V ≤ K := hred.1
  have hKV : K ≤ Subgroup.normalizer (V : Set G) := hred.2.1
  have hV2 : IsPGroup 2 V := isPGroup_two_of_sq fun x hx => hred.2.2.1.2 x hx
  have hVQ : V ≤ pCoreOf 2 K := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hVK hKV hV2
  have hV' : ⁅pCoreOf 2 K, K'⁆ ≤ V :=
    (comm_pCore_le_comm_V hK'K hKV hV2 hK' hK'V hVQ hQN).trans
      (Subgroup.le_normalizer_iff_commutator_le_left.1 (hK'K.trans hKV))
  have hD := conjClosure_le_radFreeD hK'K hKV hV'
  have hT := twoResidual_le_conjClosure hS hK'K hgen
  have hRK : twoResidual K ⊓ Subgroup.centralizer (V : Set G) ≤ K :=
    inf_le_left.trans (twoResidual_le K)
  have hKR : K ≤ Subgroup.normalizer
      ((twoResidual K ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_of (le_normalizer_twoResidual K) (le_normalizer_centralizer_of_le hKV)
  have hR2 : IsPGroup 2 (twoResidual K ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) := by
    intro g
    have hg := g.2
    obtain ⟨k, hk⟩ := exists_pow_two_eq_one hF hKV (hD (hT (Subgroup.mem_inf.1 hg).1))
      (Subgroup.mem_inf.1 hg).2
    exact ⟨k, Subtype.ext (by simpa using hk)⟩
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hRK hKR hR2

end CFSG.AGLEmbeddingD2.Tits.GN516
