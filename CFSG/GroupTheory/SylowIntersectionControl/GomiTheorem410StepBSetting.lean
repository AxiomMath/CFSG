module

public import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410
public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup
import CFSG.Quasithin.Background.B2FactorizationBaumannAux
import CFSG.GroupTheory.SylowIntersectionControl.GomiTheorem410StepBW
import CFSG.GroupTheory.SubnormalMinimal
import CFSG.GroupTheory.NatL2SectionIrreducible
import CFSG.GroupTheory.SylowIntersectionControl.GomiOverCore
import CFSG.GroupTheory.SylowIntersectionControl.GomiFactsGF2
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.RankThree.PartTwo.Sec19.SimsTheoremCShort

public section

namespace CFSG.GroupTheory

open CFSG CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.RankThree.PartOne Subgroup
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω] {f : PSubgroupSelection 2 Ω}
  {hyp : Subgroup Ω → Prop} {G : Subgroup Ω}

structure IsGomi410bSetting (G S L H W : Subgroup Ω) : Prop where
  le : L ≤ G
  subnormal : (L.subgroupOf G).IsSubnormal
  eq_sup : H = L ⊔ S ⊔ (G ⊓ centralizer (gomiV G : Set Ω))
  le_normalizer : H ≤ normalizer (L : Set Ω)
  le_gomiV : W ≤ gomiV G
  le_normalizer_W : H ≤ normalizer (W : Set Ω)
  le_centralizer_of_normal : ∀ N : Subgroup Ω, N ≤ H → H ≤ normalizer (N : Set Ω) →
    (∀ x ∈ N, ∃ k : ℕ, x ^ 2 ^ k ∈ centralizer (W : Set Ω)) → N ≤ centralizer (W : Set Ω)
  commutator_le : ⁅pCoreOf 2 G, L⁆ ≤ W
  inf_centralizer_le : L ⊓ centralizer (W : Set Ω) ≤ pCoreOf 2 G
  not_thompsonJ_le : ¬ thompsonJ S ≤ centralizer (W : Set Ω)

omit [Finite Ω] in
theorem IsGomi410bSetting.isMulCommutative {S L H W : Subgroup Ω}
    (hset : IsGomi410bSetting G S L H W) : IsMulCommutative ↥W :=
  ⟨⟨fun a b => Subtype.ext (congrArg Subtype.val
    ((B2F.isElemAbelian_omegaOneCenterOf (pCoreOf 2 G)).1.is_comm.comm
      ⟨a, hset.le_gomiV a.2⟩ ⟨b, hset.le_gomiV b.2⟩) :)⟩⟩

omit [Finite Ω] in
private theorem mul_commutator_mul_inv_bset {h q g : Ω} :
    h * ⁅h⁻¹ * q * h, g⁆ * h⁻¹ = ⁅q, h * g * h⁻¹⁆ := by
  rw [conjugate_commutatorElement]
  congr 1
  group

omit [Finite Ω] in
private theorem eq_top_of_isPGroup_quotient_bset {X : Subgroup Ω} (hX : twoResidual X = X)
    {N : Subgroup X} [hN : N.Normal] (h2 : IsPGroup 2 (X ⧸ N)) : N = ⊤ := by
  set M : Subgroup Ω := N.map X.subtype with hM
  have hXM : X ≤ Subgroup.normalizer (M : Set Ω) := by
    rw [Subgroup.le_normalizer_iff]
    intro x hx m hm
    obtain ⟨n, hn, rfl⟩ := hm
    let x' : X := ⟨x, hx⟩
    have hn' : x' * n * x'⁻¹ ∈ N := hN.conj_mem n hn x'
    simpa [M, x'] using Subgroup.mem_map_of_mem X.subtype hn'
  have h2mem : ∀ y ∈ X, ∃ k : ℕ, y ^ 2 ^ k ∈ M := by
    intro y hy
    obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp h2 (QuotientGroup.mk' N ⟨y, hy⟩)
    refine ⟨k, ?_⟩
    have hk' : ((⟨y, hy⟩ : X) ^ 2 ^ k : X) ∈ N := by
      have hk'' : QuotientGroup.mk' N ((⟨y, hy⟩ : X) ^ 2 ^ k) = 1 := by
        rw [map_pow]
        exact hk
      exact (QuotientGroup.eq_one_iff _).mp (by simpa using hk'')
    simpa [M] using Subgroup.mem_map_of_mem X.subtype hk'
  have hXM' : X ≤ M := by
    rw [← hX]
    exact CFSG.Quasithin.twoResidual_le_of_isTwoQuotient (Subgroup.map_subtype_le N) hXM h2mem
  rw [eq_top_iff]
  intro x _
  obtain ⟨n, hn, hnx⟩ := hXM' x.2
  have : n = x := Subtype.ext hnx
  simpa [this] using hn

omit [Finite Ω] in
private theorem commutator_gomiV_ne_bot_bset {S X : Subgroup Ω}
    (hX : IsGomiSingularSubgroup G S X) : (⁅gomiV G, X⁆ : Subgroup Ω) ≠ ⊥ := by
  obtain ⟨C', n, hn, hnat⟩ := hX.natural
  obtain ⟨F, _, _, hcard, α, _, _, β, hβsurj, _, _⟩ := hnat
  have hF : Nontrivial F :=
    Fintype.one_lt_card_iff_nontrivial.mp (by
      rw [hcard]
      exact Nat.one_lt_two_pow (Nat.one_le_iff_ne_zero.mp hn))
  have hβnt : Nontrivial (Multiplicative (Fin 2 → F)) :=
    @Function.nontrivial (Fin 2) F inferInstance hF
  have hnt : Nontrivial ↥(⁅gomiV G, X⁆ : Subgroup Ω) :=
    @Function.Surjective.nontrivial _ _ hβnt β hβsurj
  exact (Subgroup.nontrivial_iff_ne_bot _).mp hnt

omit [Finite Ω] in
private theorem not_le_centralizer_bset {X L W : Subgroup Ω} (hXL : X ≤ L)
    (hW : (L ⊔ (G ⊓ centralizer (gomiV G : Set Ω))) ⊓ centralizer (W : Set Ω) ≤
      centralizer (gomiV G : Set Ω))
    (hne : (⁅gomiV G, X⁆ : Subgroup Ω) ≠ ⊥) : ¬ X ≤ centralizer (W : Set Ω) := by
  intro hXW
  apply hne
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact (le_inf (hXL.trans le_sup_left) hXW).trans hW

private theorem commutator_gomiV_le_bset {S X W H : Subgroup Ω}
    (hX : IsGomiSingularSubgroup G S X) (hXH : X ≤ H)
    (hWH : H ≤ normalizer (W : Set Ω)) (hWV : W ≤ gomiV G)
    (hV2 : IsPGroup 2 (gomiV G)) (hXV : X ≤ normalizer (gomiV G : Set Ω))
    (hnot : ¬ X ≤ centralizer (W : Set Ω)) :
    (⁅gomiV G, X⁆ : Subgroup Ω) ≤ W := by
  obtain ⟨C', n, hn, hnat⟩ := hX.natural
  exact CFSG.Quasithin.commutator_le_of_isNatL2Section hV2 hX.twoResidual_eq hXV hWV
    (hXH.trans hWH) hnat hnot

private theorem commutator_pCoreOf_le_of_commutator_gomiV_bset {S X W : Subgroup Ω}
    (hX : IsGomiSingularSubgroup G S X) (hVW : (⁅gomiV G, X⁆ : Subgroup Ω) ≤ W) :
    (⁅pCoreOf 2 G, X⁆ : Subgroup Ω) ≤ W := by
  have hQ2 : IsPGroup 2 (pCoreOf 2 G) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 G
  have hXQ : X ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
    hX.le.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G)
  have hJ : ∀ (N : Subgroup X) [N.Normal], IsPGroup 2 (X ⧸ N) → N = ⊤ :=
    fun N _ hN => eq_top_of_isPGroup_quotient_bset hX.twoResidual_eq hN
  have hsims := CFSG.RankThree.PartTwo.Sec19.SimsTheoremC.commutator_commutator_eq_of_twoResidual
    hJ hQ2 hXQ
  calc ⁅pCoreOf 2 G, X⁆ = ⁅⁅pCoreOf 2 G, X⁆, X⁆ := hsims.symm
    _ ≤ ⁅gomiV G, X⁆ := Subgroup.commutator_mono hX.commutator_pCoreOf_le le_rfl
    _ ≤ W := hVW

private def normalizerCommutator_bset (Q W : Subgroup Ω) : Subgroup Ω where
  carrier := {g | g ∈ Subgroup.normalizer (W : Set Ω) ∧ ∀ q ∈ Q, ⁅q, g⁆ ∈ W}
  mul_mem' := by
    rintro a b ⟨haN, ha⟩ ⟨hbN, hb⟩
    refine ⟨(Subgroup.normalizer (W : Set Ω)).mul_mem haN hbN, fun q hq => ?_⟩
    have h2 : a * ⁅q, b⁆ * a⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp haN (⁅q, b⁆)).mp (hb q hq)
    have h1 : ⁅q, a⁆ * (a * ⁅q, b⁆ * a⁻¹) ∈ W := W.mul_mem (ha q hq) h2
    rw [commutatorElement_mul_right_eq_mul_conj]
    simpa [mul_assoc] using h1
  one_mem' := ⟨(Subgroup.normalizer (W : Set Ω)).one_mem, by
    intro q hq
    rw [commutatorElement_def]
    simp⟩
  inv_mem' := by
    rintro a ⟨haN, ha⟩
    refine ⟨(Subgroup.normalizer (W : Set Ω)).inv_mem haN, fun q hq => ?_⟩
    have h3 : ⁅a, q⁆ ∈ W := by rw [← commutatorElement_inv]; exact W.inv_mem (ha q hq)
    have h2 : a⁻¹ * ⁅a, q⁆ * a ∈ W := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (W : Set Ω)).inv_mem haN) (⁅a, q⁆)).mp h3
    rw [commutatorElement_inv_right]
    exact h2

omit [Finite Ω] in
private theorem mem_normalizerCommutator_bset {Q W : Subgroup Ω} {g : Ω} :
    g ∈ normalizerCommutator_bset Q W ↔
      g ∈ Subgroup.normalizer (W : Set Ω) ∧ ∀ q ∈ Q, ⁅q, g⁆ ∈ W :=
  Iff.rfl

omit [Finite Ω] in
private theorem le_normalizer_normalizerCommutator_bset {Q W : Subgroup Ω}
    (hGQ : G ≤ Subgroup.normalizer (Q : Set Ω)) :
    G ⊓ Subgroup.normalizer (W : Set Ω) ≤
      Subgroup.normalizer (normalizerCommutator_bset Q W : Set Ω) := by
  refine (Subgroup.le_normalizer_iff).mpr fun h hh g hg => ?_
  rw [mem_normalizerCommutator_bset]
  have hq' : ∀ q ∈ Q, ⁅q, h * g * h⁻¹⁆ ∈ W := by
    intro q hq
    have hq'' : h⁻¹ * q * h ∈ Q :=
      (Subgroup.mem_normalizer_iff''.mp (hGQ hh.1) q).mp hq
    have hcomm : ⁅h⁻¹ * q * h, g⁆ ∈ W :=
      (mem_normalizerCommutator_bset.mp hg).2 _ hq''
    have hconj : h * ⁅h⁻¹ * q * h, g⁆ * h⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.mp hh.2 (⁅h⁻¹ * q * h, g⁆)).mp hcomm
    rwa [mul_commutator_mul_inv_bset] at hconj
  exact ⟨(Subgroup.normalizer (W : Set Ω)).mul_mem
    ((Subgroup.normalizer (W : Set Ω)).mul_mem hh.2 (mem_normalizerCommutator_bset.mp hg).1)
    ((Subgroup.normalizer (W : Set Ω)).inv_mem hh.2), hq'⟩

omit [Finite Ω] in
private theorem commutator_pCoreOf_le_bset {S X L W : Subgroup Ω}
    (hHG : L ⊔ S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤ G)
    (hHnormW : L ⊔ S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤ normalizer (W : Set Ω))
    (hXL : X ≤ L) (hQXW : (⁅pCoreOf 2 G, X⁆ : Subgroup Ω) ≤ W)
    (hmin : ∀ N : Subgroup Ω,
      L ⊔ (S ⊔ (G ⊓ centralizer (gomiV G : Set Ω))) ≤ normalizer (N : Set Ω) →
        X ≤ N → L ≤ N) :
    (⁅pCoreOf 2 G, L⁆ : Subgroup Ω) ≤ W := by
  have hGQ : G ≤ Subgroup.normalizer (pCoreOf 2 G : Set Ω) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 G
  have hGN := le_normalizer_normalizerCommutator_bset (Q := pCoreOf 2 G) (W := W) hGQ
  have hHN : L ⊔ S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤
      Subgroup.normalizer (normalizerCommutator_bset (pCoreOf 2 G) W : Set Ω) :=
    (le_inf hHG hHnormW).trans hGN
  have hXH : X ≤ L ⊔ S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) :=
    hXL.trans (le_sup_left.trans le_sup_left)
  have hXN : X ≤ normalizerCommutator_bset (pCoreOf 2 G) W := by
    intro x hx
    exact ⟨hHnormW (hXH hx),
      fun q hq => Subgroup.commutator_le.mp hQXW q hq x hx⟩
  have hLN : L ≤ normalizerCommutator_bset (pCoreOf 2 G) W :=
    hmin (normalizerCommutator_bset (pCoreOf 2 G) W)
      (by simpa only [sup_assoc] using hHN) hXN
  exact Subgroup.commutator_le.mpr fun q hq l hl =>
    (mem_normalizerCommutator_bset.mp (hLN hl)).2 q hq

omit [Finite Ω] in
private theorem le_normalizer_centralizer_bset {X H : Subgroup Ω}
    (hX : X ≤ normalizer (H : Set Ω)) :
    X ≤ normalizer (centralizer (H : Set Ω) : Set Ω) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx c hc
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro w hw
  have hxw : x⁻¹ * w * x ∈ H := (Subgroup.mem_normalizer_iff''.mp (hX hx) w).mp hw
  have hcw : (x⁻¹ * w * x) * c = c * (x⁻¹ * w * x) := hc _ hxw
  calc w * (x * c * x⁻¹) = x * ((x⁻¹ * w * x) * c) * x⁻¹ := by group
    _ = x * (c * (x⁻¹ * w * x)) * x⁻¹ := by rw [hcw]
    _ = (x * c * x⁻¹) * w := by group

private theorem inf_centralizer_le_bset (hchar : CharTwo G) {L W : Subgroup Ω}
    (hLG : L ≤ G) (hWV : W ≤ gomiV G) (hcomm : (⁅pCoreOf 2 G, L⁆ : Subgroup Ω) ≤ W)
    (hLC : (L ⊔ (G ⊓ centralizer (gomiV G : Set Ω))) ⊓ centralizer (W : Set Ω) ≤
      centralizer (gomiV G : Set Ω)) :
    L ⊓ centralizer (W : Set Ω) ≤ pCoreOf 2 G := by
  intro g hg
  exact mem_pCoreOf_of_commutator_mem_gomiV hchar (hLG hg.1)
    (hLC ⟨Subgroup.mem_sup_left hg.1, hg.2⟩)
    (fun q hq => hWV (Subgroup.commutator_le.mp hcomm q hq g hg.1))

omit [Finite Ω] in
private theorem not_thompsonJ_le_bset {S X W : Subgroup Ω}
    (hX : IsGomiSingularSubgroup G S X) (hXW : X ≤ normalizer (W : Set Ω))
    (hne : ¬ X ≤ centralizer (W : Set Ω)) :
    ¬ thompsonJ S ≤ centralizer (W : Set Ω) := by
  intro hJ
  apply hne
  rw [hX.eq_commutator_thompsonJ]
  refine (Subgroup.commutator_le).mpr fun x hx j hj => ?_
  have hxNC := le_normalizer_centralizer_bset (X := X) (H := W) hXW hx
  have hjC : j ∈ Subgroup.centralizer (W : Set Ω) := hJ hj
  have h1 : x * j * x⁻¹ ∈ Subgroup.centralizer (W : Set Ω) :=
    (Subgroup.mem_normalizer_iff.mp hxNC j).mp hjC
  have h2 : j⁻¹ ∈ Subgroup.centralizer (W : Set Ω) :=
    (Subgroup.centralizer (W : Set Ω)).inv_mem hjC
  rw [commutatorElement_def]
  exact (Subgroup.centralizer (W : Set Ω)).mul_mem h1 h2

theorem Gomi410Cex.exists_isGomi410bSetting (h : Gomi410Cex f hyp G)
    (hfZ : ∀ P : Subgroup Ω, IsPGroup 2 P → omegaOneCenterOf P ∈ f.sets P)
    (hchar : CharTwo G) (hmono : ∀ H : Subgroup Ω, H ≤ G → pCoreOf 2 G ≤ H → hyp H)
    {S X : Subgroup Ω} (hS : IsSylowTwoOf S G) (hX : IsGomiSingularSubgroup G S X) :
    ∃ L H W : Subgroup Ω, IsGomi410bSetting G S L H W := by
  have hTG : S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤ normalizer (G : Set Ω) :=
    sup_le (hS.1.trans Subgroup.le_normalizer) (inf_le_left.trans Subgroup.le_normalizer)
  obtain ⟨L, hXL, hLG, hLsn, hTnormL, hmin⟩ :=
    exists_isSubnormal_minimal (X := X) (T := S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)))
      hX.le hTG
  have hSL : S ≤ normalizer (L : Set Ω) := le_sup_left.trans hTnormL
  have hCL : G ⊓ centralizer (gomiV G : Set Ω) ≤ normalizer (L : Set Ω) :=
    le_sup_right.trans hTnormL
  obtain ⟨W, hWV, hHW, hWcent, hWLC⟩ :=
    Gomi410Cex.exists_W h hfZ hchar hmono hS hLG hLsn hSL hCL
  have hV2 : IsPGroup 2 (gomiV G) :=
    CFSG.Open.IsElemAbelian.isPGroup (gomiV_moduleSetting G).1
  have hXV : X ≤ Subgroup.normalizer (gomiV G : Set Ω) :=
    hX.le.trans (gomiV_moduleSetting G).2
  have hne : (⁅gomiV G, X⁆ : Subgroup Ω) ≠ ⊥ := commutator_gomiV_ne_bot_bset hX
  have hnotW : ¬ X ≤ Subgroup.centralizer (W : Set Ω) :=
    not_le_centralizer_bset hXL hWLC hne
  have hXH : X ≤ L ⊔ S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) :=
    hXL.trans (le_sup_left.trans le_sup_left)
  have hVW : (⁅gomiV G, X⁆ : Subgroup Ω) ≤ W :=
    commutator_gomiV_le_bset hX hXH hHW hWV hV2 hXV hnotW
  have hQXW : (⁅pCoreOf 2 G, X⁆ : Subgroup Ω) ≤ W :=
    commutator_pCoreOf_le_of_commutator_gomiV_bset hX hVW
  have hHG : L ⊔ S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)) ≤ G :=
    sup_le (sup_le hLG hS.1) inf_le_left
  have hQL : (⁅pCoreOf 2 G, L⁆ : Subgroup Ω) ≤ W :=
    commutator_pCoreOf_le_bset hHG hHW hXL hQXW hmin
  refine ⟨L, L ⊔ S ⊔ (G ⊓ centralizer (gomiV G : Set Ω)), W,
    hLG, hLsn, rfl, ?_, hWV, hHW, hWcent, hQL, ?_, ?_⟩
  · rw [sup_assoc]
    exact sup_le Subgroup.le_normalizer hTnormL
  · exact inf_centralizer_le_bset hchar hLG hWV hQL hWLC
  · exact not_thompsonJ_le_bset hX (hXH.trans hHW) hnotW

end CFSG.GroupTheory