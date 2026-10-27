module

public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Four
public import CFSG.CGT.PushingUpLit.LIT.Foote.L56Comm

public section

namespace CFSG.CGT.PushingUpLit.LIT.Foote

open CFSG CFSG.RankThree.PartOne CFSG.CGT.PushingUpLit CFSG.CGT.PushingUp CFSG.Assembly
open CFSG.ABGLocalTools
open CFSG.ComponentClassification.AschbacherTightEmbedding
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_blockU {J : Subgroup G} {g : G} (hg : g ∈ Subgroup.normalizer (J : Set G)) :
    g ∈ Subgroup.normalizer (blockU J : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact fun hy => conj_mem_blockU hg hy
  · intro hy
    have := conj_mem_blockU ((Subgroup.normalizer (J : Set G)).inv_mem hg) hy
    have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
    rwa [e] at this

namespace CE

variable {M J : Subgroup G} (c : CE G M J)
include c

theorem mem_normalizer_conj_of_centralizes {g : G} {T : Subgroup G} (hT : T ≤ rightConjugate J g)
    (hT2 : IsPGroup 2 T) (hT1 : T ≠ ⊥)
    (hnc : ∃ t ∈ T, ∃ k ∈ rightConjugate J g, t * k ≠ k * t) {q : G}
    (hq : ∀ t ∈ T, q * t = t * q) :
    q ∈ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) := by
  obtain ⟨t₀, ht₀T, ht₀1, ht₀2⟩ := exists_involution_of_isPGroup hT2 hT1
  have hC := c.centralizer_le_conj (hT ht₀T) ⟨1, by rw [pow_one, pow_two]; exact ht₀2⟩ ht₀1
  have hqM : q ∈ rightConjugate M g :=
    hC (Subgroup.mem_centralizer_singleton_iff.2 (hq t₀ ht₀T))
  by_contra hqn
  have hne : rightConjugate (rightConjugate J g) q ≠ rightConjugate J g :=
    fun h => hqn ((rightConjugate_eq_self_iff _ q).1 h)
  have hcomm := (c.transport g).commutator_conj_eq_bot hqM hne
  have hJC : rightConjugate J g ≤
      Subgroup.centralizer ((rightConjugate (rightConjugate J g) q : Subgroup G) : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
  obtain ⟨t, htT, k, hk, htk⟩ := hnc
  apply htk
  have htq : t ∈ rightConjugate (rightConjugate J g) q := by
    rw [mem_rightConjugate_iff]
    have : q * t * q⁻¹ = t := by rw [hq t htT]; group
    rw [this]
    exact hT htT
  exact Subgroup.mem_centralizer_iff.1 (hJC hk) t htq

theorem commutator_le_blockU_of_le_oTwoIn {T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (J : Set G)) (hO2 : ⁅J, T⁆ ≤ oTwoIn J) :
    ⁅J, T⁆ ≤ blockU J := by
  have hJ := c.block
  have hTJ' : ⁅T, J⁆ = ⁅J, T⁆ := Subgroup.commutator_comm T J
  have hV : ⁅⁅J, T⁆, J⁆ ≤ blockU J := Subgroup.commutator_mono hO2 le_rfl
  have hHV : J ⊔ T ≤ Subgroup.normalizer (blockU J : Set G) :=
    sup_le (le_normalizer_blockU J) (fun t ht => mem_normalizer_blockU (hTN ht))
  have h := commutator_commutator_le_of_rotate (H := J ⊔ T) (H₁ := J) (H₂ := J) (H₃ := T)
    (N := blockU J) le_sup_left le_sup_left le_sup_right ((blockU_le J).trans le_sup_left) hHV
    hV (by rw [hTJ']; exact hV)
  rwa [hJ.perfect] at h

theorem commutator_le_blockU_of_centralizes {T : Subgroup G}
    (hTN : T ≤ Subgroup.normalizer (J : Set G)) (hT : ∀ t ∈ T, ∀ v ∈ blockU J, t * v = v * t) :
    ⁅J, T⁆ ≤ blockU J := by
  have hJ := c.block
  have hTC : T ≤ Subgroup.centralizer (blockU J : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun v hv => (hT t ht v hv).symm
  have h0 : ⁅T, blockU J⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hTC
  have h1 : ⁅⁅J, T⁆, blockU J⁆ = ⊥ := by
    refine Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := J) (H₂ := T)
      (H₃ := blockU J) ?_ ?_
    · rw [h0]
      exact Subgroup.commutator_bot_left _
    · rw [hJ.blockU_stable, Subgroup.commutator_comm]
      exact h0
  have hJTle : ⁅J, T⁆ ≤ J := Subgroup.le_normalizer_iff_commutator_le_left.1 hTN
  have hJTC : ⁅J, T⁆ ≤ J ⊓ Subgroup.centralizer (blockU J : Set G) :=
    le_inf hJTle (Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1)
  have hO : ⁅⁅J, T⁆, J⁆ ≤ oTwoIn J :=
    (Subgroup.commutator_mono hJTC le_rfl).trans hJ.commutator_centralizer_le
  have hTJ' : ⁅T, J⁆ = ⁅J, T⁆ := Subgroup.commutator_comm T J
  have hH : J ⊔ T ≤ Subgroup.normalizer (oTwoIn J : Set G) :=
    sup_le (SixThree.le_normalizer_oTwoIn J)
      (hTN.trans (SixThree.normalizer_le_normalizer_oTwoIn J))
  have hO2 : ⁅J, T⁆ ≤ oTwoIn J := by
    have h := commutator_commutator_le_of_rotate (H := J ⊔ T) (H₁ := J) (H₂ := J) (H₃ := T)
      (N := oTwoIn J) le_sup_left le_sup_left le_sup_right ((oTwoIn_le J).trans le_sup_left) hH
      hO (by rw [hTJ']; exact hO)
    rwa [hJ.perfect] at h
  exact c.commutator_le_blockU_of_le_oTwoIn hTN hO2

theorem not_centralizes_blockU (hA : FooteTheoremA) {z₀ : G} (hz : ZData J z₀) {g : G}
    {T : Subgroup G} (hgood : Good56 M J g) (hT : ABGLocalTools.IsSylowOf 2 T (eSub J g))
    (hmax : ∀ h, Good56 M J h →
      (Nat.card ↥(eSub J h)).factorization 2 ≤ (Nat.card ↥(eSub J g)).factorization 2) :
    ¬ ∀ t ∈ T, ∀ v ∈ blockU J, t * v = v * t := by
  intro hcent
  have hJ := c.block
  have hg : g ∉ M := hgood.1
  obtain ⟨W, hWle, hW2, hW4⟩ := hgood.2
  have hW1 : W ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hW4
    omega
  have hWp : IsPGroup 2 W := IsPGroup.of_card (n := 2) (by rw [hW4]; norm_num)
  have hT1 : T ≠ ⊥ := ne_bot_of_isSylowOf_even hT (even_card_of_isPGroup hWp hW1 hWle)
  have hTE : T ≤ eSub J g := hT.le
  have hTJg : T ≤ rightConjugate J g := hTE.trans inf_le_left
  have hTN : T ≤ Subgroup.normalizer (J : Set G) := hTE.trans inf_le_right
  have hT2 : IsPGroup 2 T := hT.isPGroup
  have hnc := c.exists_noncentral hA hz hg hT hT1
  have hcentN : ∀ q : G, (∀ t ∈ T, q * t = t * q) →
      q ∈ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) :=
    fun q hq => c.mem_normalizer_conj_of_centralizes hTJg hT2 hT1 hnc hq
  have hZ2 : IsPGroup 2 ↥(zSub M z₀ ⊓ J) := (c.isPGroup_zSub hz).to_le inf_le_left
  have hZ0 : (zSub M z₀ ⊓ J) ≠ ⊥ := by
    have hz0mem : z₀ ∈ zSub M z₀ ⊓ J := ⟨z₀_mem, hz.mem⟩
    intro h
    rw [h, Subgroup.mem_bot] at hz0mem
    exact hz.ne_one hz0mem
  have hTZ : T ≤ Subgroup.normalizer ((zSub M z₀ ⊓ J : Subgroup G) : Set G) := by
    intro t ht
    have htM : t ∈ M := c.normalizer_le_M (hTN ht)
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hy1, hy2⟩
      exact ⟨zSub_conj htM hy1, (Subgroup.mem_normalizer_iff.1 (hTN ht) y).1 hy2⟩
    · rintro ⟨hy1, hy2⟩
      refine ⟨?_, (Subgroup.mem_normalizer_iff.1 (hTN ht) y).2 hy2⟩
      have h := zSub_conj (M.inv_mem htM) hy1
      have e : t⁻¹ * (t * y * t⁻¹) * t⁻¹⁻¹ = y := by group
      rwa [e] at h
  have hCne := SignalizerFunctorTheorem.Glauberman.Steps678.inf_centralizer_ne_bot Nat.prime_two
    hT2 hZ2 hZ0 hTZ
  obtain ⟨⟨ζ, hζ⟩, hζ1'⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hCne
  have hζ1 : ζ ≠ 1 := fun h => hζ1' (Subtype.ext h)
  obtain ⟨hζZJ, hζT⟩ := Subgroup.mem_inf.1 hζ
  obtain ⟨hζZ, hζJ⟩ := Subgroup.mem_inf.1 hζZJ
  set C : Subgroup G := zSub M z₀ ⊓ J ⊓ Subgroup.centralizer (T : Set G) with hCdef
  have hCcen : ∀ b ∈ C, ∀ j ∈ J, b * j = j * b := fun b hb j hj => by
    have hbZ : b ∈ zSub M z₀ := (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).1).1
    exact c.zSub_centralizes hz hbZ M.one_mem (by rw [rightConjugate_one]; exact hj)
  have hCsq : ∀ b ∈ C, b * b = 1 := fun b hb =>
    c.zSub_sq hz (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).1).1
  have hCJ : ∀ b ∈ C, b ∈ J := fun b hb => (Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hb).1).2
  have hCT : ∀ b ∈ C, ∀ t ∈ T, t * b = b * t := fun b hb t ht =>
    Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 hb).2 t ht
  have hCc : ∀ b ∈ C, ∀ b' ∈ C, b * b' = b' * b := fun b hb b' hb' => hCcen b hb b' (hCJ b' hb')
  have hζC : ζ ∈ C := hζ
  have hVC : ∀ a ∈ blockU J, ∀ b ∈ C, a * b = b * a := fun a ha b hb =>
    (hCcen b hb a (blockU_le J ha)).symm
  have hmem : ∀ x ∈ blockU J ⊔ C, ∃ a ∈ blockU J, ∃ b ∈ C, x = a * b := fun x hx =>
    (mem_sup_iff_of_commute hVC).1 hx
  have hVc : ∀ a ∈ blockU J, ∀ b ∈ blockU J, a * b = b * a := hJ.blockU_comm
  have hVs : ∀ a ∈ blockU J, a * a = 1 := hJ.blockU_sq_eq_one
  have hV'c : ∀ x ∈ blockU J ⊔ C, ∀ y ∈ blockU J ⊔ C, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    obtain ⟨a', ha', b', hb', rfl⟩ := hmem y hy
    have e1 : a * b * (a' * b') = a * a' * (b * b') := by
      calc a * b * (a' * b') = a * (b * a') * b' := by group
        _ = a * (a' * b) * b' := by rw [(hVC a' ha' b hb).symm]
        _ = a * a' * (b * b') := by group
    have e2 : a' * b' * (a * b) = a' * a * (b' * b) := by
      calc a' * b' * (a * b) = a' * (b' * a) * b := by group
        _ = a' * (a * b') * b := by rw [(hVC a ha b' hb').symm]
        _ = a' * a * (b' * b) := by group
    rw [e1, e2, hVc a ha a' ha', hCc b hb b' hb']
  have hV's : ∀ x ∈ blockU J ⊔ C, x * x = 1 := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem x hx
    have e1 : a * b * (a * b) = a * a * (b * b) := by
      calc a * b * (a * b) = a * (b * a) * b := by group
        _ = a * (a * b) * b := by rw [(hVC a ha b hb).symm]
        _ = a * a * (b * b) := by group
    rw [e1, hVs a ha, hCsq b hb, mul_one]
  have hV'x : ∀ x ∈ J, ∀ v ∈ blockU J ⊔ C, x * v * x⁻¹ ∈ blockU J ⊔ C := by
    intro x hx v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem v hv
    have e : x * (a * b) * x⁻¹ = (x * a * x⁻¹) * b := by
      have hxb : x * b = b * x := (hCcen b hb x hx).symm
      calc x * (a * b) * x⁻¹ = x * a * (b * x⁻¹) := by group
        _ = x * a * (x⁻¹ * b) := by
          have : b * x⁻¹ = x⁻¹ * b := by
            calc b * x⁻¹ = x⁻¹ * (x * b) * x⁻¹ := by group
              _ = x⁻¹ * (b * x) * x⁻¹ := by rw [hxb]
              _ = x⁻¹ * b := by group
          rw [this]
        _ = (x * a * x⁻¹) * b := by group
    rw [e]
    exact Subgroup.mul_mem _
      (Subgroup.mem_sup_left (conj_mem_blockU (Subgroup.le_normalizer hx) ha))
      (Subgroup.mem_sup_right hb)
  have hV'T : ∀ t ∈ T, ∀ v ∈ blockU J ⊔ C, t * v = v * t := by
    intro t ht v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem v hv
    calc t * (a * b) = (t * a) * b := by group
      _ = (a * t) * b := by rw [hcent t ht a ha]
      _ = a * (t * b) := by group
      _ = a * (b * t) := by rw [hCT b hb t ht]
      _ = a * b * t := by group
  have hV'J : blockU J ⊔ C ≤ J := sup_le (blockU_le J) hCJ
  have hV'N : blockU J ⊔ C ≤ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) := by
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := hmem v hv
    have h1 : a ∈ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) :=
      hcentN a fun t ht => (hcent t ht a ha).symm
    have h2 : b ∈ Subgroup.normalizer ((rightConjugate J g : Subgroup G) : Set G) :=
      hcentN b fun t ht => (hCT b hb t ht).symm
    exact Subgroup.mul_mem _ h1 h2
  have hV'p : IsPGroup 2 ↥(blockU J ⊔ C) := fun x => ⟨1, Subtype.ext (by
    simpa [pow_two] using hV's x x.2)⟩
  have hV'card : Nat.card (blockU J ⊔ C : Subgroup G) ≤ Nat.card T :=
    c.card_le_of_le_normalizer hA hz hgood hT hmax hV'J hV'N hV'p
  have hTJV : ⁅J, T⁆ ≤ blockU J := c.commutator_le_blockU_of_centralizes hTN hcent
  have hodd : ∀ x ∈ J, Odd (orderOf x) → x ∈ rightConjugate M g := by
    intro x hxJ hxo
    have hTx : ∀ t ∈ T, ⁅t, x⁆ ∈ blockU J ⊔ C := fun t ht =>
      Subgroup.mem_sup_left (hTJV (by
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator ht hxJ))
    obtain ⟨t, htT, ht1, htx⟩ := exists_centralizes_of_card hxo (pow_orderOf_eq_one x) hV'c hV's
      (hV'x x hxJ) hV'T hTx ⟨ζ, Subgroup.mem_sup_right hζC, hζ1, (hCcen ζ hζC x hxJ)⟩ hV'card
    have ht2 : ∃ n : ℕ, t ^ 2 ^ n = 1 := by
      obtain ⟨n, hn⟩ := hT2 ⟨t, htT⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    have hC' := c.centralizer_le_conj (hTJg htT) ht2 ht1
    exact hC' (Subgroup.mem_centralizer_singleton_iff.2 htx.symm)
  have hJM : J ≤ rightConjugate M g := by
    refine hJ.le_closure_odd.trans ((Subgroup.closure_le _).2 fun x hx => hodd x hx.1 hx.2)
  apply hg
  have : rightConjugate J g⁻¹ ≤ M := by
    intro y hy
    rw [mem_rightConjugate_iff] at hy
    have h1 := hJM hy
    rw [mem_rightConjugate_iff] at h1
    have e : g * (g⁻¹ * y * g⁻¹⁻¹) * g⁻¹ = y := by group
    rwa [e] at h1
  have := c.mem_of_conj_le this
  simpa using M.inv_mem this

end CE

end CFSG.CGT.PushingUpLit.LIT.Foote
