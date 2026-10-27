module

public import CFSG.GroupTheory.SylowIntersectionControl.SingularSubgroup.GenerationCentralizer
import CFSG.Quasithin.Background.AutOnSylow
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3NineTheta
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6Basic
import CFSG.Quasithin.Background.SmithC27Setup

public section

namespace CFSG.GroupTheory.GomiThm45Counterexample

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {Ω : Type} [Group Ω] [Finite Ω] {c : GNPairChoice Ω} {G S : Subgroup Ω}

omit [Finite Ω] in
private noncomputable def preimage_g45ic {W : Subgroup Ω} (M : Subgroup Ω)
    (hM : M ≤ Subgroup.normalizer (W : Set Ω)) (P : Subgroup (MulAut ↥W)) : Subgroup Ω :=
  Subgroup.map M.subtype (Subgroup.comap (A4.actionOn W M hM) P)

omit [Finite Ω] in
private theorem mem_preimage_g45ic {W M : Subgroup Ω}
    {hM : M ≤ Subgroup.normalizer (W : Set Ω)} {P : Subgroup (MulAut ↥W)} {x : Ω}
    (hx : x ∈ M) :
    x ∈ preimage_g45ic M hM P ↔ A4.actionOn W M hM ⟨x, hx⟩ ∈ P := by
  constructor
  · intro h
    obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.1 h
    have hyP : A4.actionOn W M hM y ∈ P := Subgroup.mem_comap.1 hy
    rwa [show y = ⟨x, hx⟩ from Subtype.ext hxy] at hyP
  · intro hxP
    exact Subgroup.mem_map.2 ⟨⟨x, hx⟩, Subgroup.mem_comap.2 hxP, rfl⟩

omit [Finite Ω] in
private theorem preimage_g45ic_le {W M : Subgroup Ω}
    {hM : M ≤ Subgroup.normalizer (W : Set Ω)} (P : Subgroup (MulAut ↥W)) :
    preimage_g45ic M hM P ≤ M :=
  Subgroup.map_subtype_le _

omit [Finite Ω] in
private theorem actionOn_eq_conjAct_g45ic {W M : Subgroup Ω}
    {hM : M ≤ Subgroup.normalizer (W : Set Ω)} {x : Ω} (hx : x ∈ M) :
    A4.actionOn W M hM ⟨x, hx⟩ = conjAct W ⟨x, hM hx⟩ := by
  show conjAct W (Subgroup.inclusion hM ⟨x, hx⟩) = conjAct W ⟨x, hM hx⟩
  congr 1

omit [Finite Ω] in
private theorem autOn_preimage_g45ic {W M : Subgroup Ω}
    {hM : M ≤ Subgroup.normalizer (W : Set Ω)} {P : Subgroup (MulAut ↥W)}
    (hPM : P ≤ autOn M W) : autOn (preimage_g45ic M hM P) W = P := by
  refine le_antisymm ?_ ?_
  · intro a ha
    obtain ⟨n, hn, rfl⟩ := AutOn.mem_autOn_iff.1 ha
    have hnM : (n : Ω) ∈ M := preimage_g45ic_le P hn
    have hnP : A4.actionOn W M hM ⟨(n : Ω), hnM⟩ ∈ P :=
      (mem_preimage_g45ic (M := M) (hM := hM) hnM).1 hn
    rw [actionOn_eq_conjAct_g45ic hnM] at hnP
    rwa [show (⟨(n : Ω), hM hnM⟩ : Subgroup.normalizer (W : Set Ω)) = n from
      Subtype.ext rfl] at hnP
  · intro p hp
    obtain ⟨n, -, rfl⟩ := (A4.mem_autOn_iff hM).1 (hPM hp)
    have hpn : (n : Ω) ∈ preimage_g45ic M hM P :=
      (mem_preimage_g45ic (M := M) (hM := hM) n.2).2 hp
    rw [actionOn_eq_conjAct_g45ic n.2]
    exact AutOn.conjAct_mem_autOn ⟨(n : Ω), hM n.2⟩ hpn

omit [Finite Ω] in
private theorem conj_mem_preimage_g45ic {W M G : Subgroup Ω}
    {hM : M ≤ Subgroup.normalizer (W : Set Ω)} {P : Subgroup (MulAut ↥W)}
    (hGW : G ≤ Subgroup.normalizer (W : Set Ω))
    (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hPG : autOn G W ≤ Subgroup.normalizer (P : Set (MulAut ↥W)))
    {g : Ω} (hg : g ∈ G) {k : Ω} (hk : k ∈ preimage_g45ic M hM P) :
    g * k * g⁻¹ ∈ preimage_g45ic M hM P := by
  have hkM : k ∈ M := preimage_g45ic_le P hk
  have hkP : A4.actionOn W M hM ⟨k, hkM⟩ ∈ P := (mem_preimage_g45ic (M := M) (hM := hM) hkM).1 hk
  have hgkM : g * k * g⁻¹ ∈ M :=
    (Subgroup.mem_normalizer_iff.mp (hGM hg) k).mp hkM
  refine (mem_preimage_g45ic (M := M) (hM := hM) hgkM).2 ?_
  have hconj : A4.actionOn W M hM ⟨g * k * g⁻¹, hgkM⟩ =
      conjAct W ⟨g, hGW hg⟩ * A4.actionOn W M hM ⟨k, hkM⟩ *
        (conjAct W ⟨g, hGW hg⟩)⁻¹ := by
    rw [actionOn_eq_conjAct_g45ic hgkM, actionOn_eq_conjAct_g45ic hkM]
    rw [show (⟨g * k * g⁻¹, hM hgkM⟩ : Subgroup.normalizer (W : Set Ω)) =
      ⟨g, hGW hg⟩ * ⟨k, hM hkM⟩ * ⟨g, hGW hg⟩⁻¹ from Subtype.ext rfl]
    rw [map_mul, map_mul, map_inv]
  rw [hconj]
  exact (Subgroup.mem_normalizer_iff.mp
    (hPG (AutOn.conjAct_mem_autOn ⟨g, hGW hg⟩ hg)) _).mp hkP

omit [Finite Ω] in
private theorem le_normalizer_preimage_g45ic {W M G : Subgroup Ω}
    {hM : M ≤ Subgroup.normalizer (W : Set Ω)} {P : Subgroup (MulAut ↥W)}
    (hGW : G ≤ Subgroup.normalizer (W : Set Ω))
    (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    (hPG : autOn G W ≤ Subgroup.normalizer (P : Set (MulAut ↥W))) :
    G ≤ Subgroup.normalizer (preimage_g45ic M hM P : Set Ω) := by
  rw [Subgroup.le_normalizer_iff]
  intro g hg k hk
  exact conj_mem_preimage_g45ic hGW hGM hPG hg hk

private theorem mem_of_odd_orderOf_of_mul_pow_two_g45ic {X : Type*} [Group X]
    {N : Subgroup X} [N.Normal] {x y n : X} (hx : Odd (orderOf x)) (hn : n ∈ N)
    (hxy : x = n * y) {k : ℕ} (hy : y ^ 2 ^ k = 1) : x ∈ N := by
  have hquot : (QuotientGroup.mk' N x) = (QuotientGroup.mk' N y) := by
    rw [hxy, map_mul, show (QuotientGroup.mk' N n) = 1 from (QuotientGroup.eq_one_iff n).mpr hn]
    exact one_mul _
  have hk : (QuotientGroup.mk' N x) ^ 2 ^ k = 1 := by
    rw [hquot, ← map_pow, hy, map_one]
  have h1 : orderOf (QuotientGroup.mk' N x) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (QuotientGroup.mk' N x) ∣ orderOf x :=
    orderOf_map_dvd (QuotientGroup.mk' N) x
  have hcop : Nat.Coprime (2 ^ k) (orderOf x) :=
    Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx)
  have h3 : orderOf (QuotientGroup.mk' N x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop h1 h2
  rw [orderOf_eq_one_iff] at h3
  exact (QuotientGroup.eq_one_iff x).mp h3

private theorem sup_preimage_g45ic (h : GomiThm45Counterexample c G S) {M : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    {P : Subgroup (MulAut ↥(gomiV M))} (hPM : P ≤ autOn M (gomiV M))
    (hPG : autOn G (gomiV M) ≤ Subgroup.normalizer (P : Set (MulAut ↥(gomiV M))))
    (h2 : 2 ∣ Nat.card P) :
    preimage_g45ic M (gomiV_moduleSetting M).2 P ⊔ S = G := by
  let W := gomiV M
  have hM : M ≤ Subgroup.normalizer (W : Set Ω) := (gomiV_moduleSetting M).2
  let K : Subgroup Ω := preimage_g45ic M hM P
  have hKM : K ≤ M := preimage_g45ic_le P
  have hKG : K ≤ G := hKM.trans hMG
  have hGW : G ≤ Subgroup.normalizer (W : Set Ω) :=
    le_normalizer_gomiV_of_le_normalizer hGM
  have hNK : G ≤ Subgroup.normalizer (K : Set Ω) := le_normalizer_preimage_g45ic hGW hGM hPG
  by_contra hne
  have hK_sylow : IsSylowTwoOf (pCoreOf 2 K) K :=
    isSylowTwoOf_pCoreOf_of_sup_ne h hKG hNK hne
  have hQK_M : pCoreOf 2 K ≤ M := (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKM
  have hM_NQK : M ≤ Subgroup.normalizer (pCoreOf 2 K : Set Ω) :=
    (hMG.trans hNK).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
  have hQK_R : pCoreOf 2 K ≤ pCoreOf 2 M :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQK_M hM_NQK
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have hQK_CW : pCoreOf 2 K ≤ Subgroup.centralizer (W : Set Ω) :=
    hQK_R.trans (CFSG.Quasithin.SmithC27.pCoreOf_le_centralizer_omegaOneCenterOf M)
  have hK_NW : K ≤ Subgroup.normalizer (W : Set Ω) := hKM.trans hM
  have hsylow : IsSylowTwoOf (autOn (pCoreOf 2 K) W) (autOn K W) :=
    AutOn.isSylowTwoOf_autOn hK_sylow hK_NW
  have hautK : autOn K W = P := autOn_preimage_g45ic hPM
  rw [AutOn.autOn_eq_bot_of_le_centralizer hQK_CW, hautK] at hsylow
  have hodd : Odd (Nat.card P) :=
    CFSG.ComponentClassification.AschbacherTheorem3.odd_of_isSylowOf_bot
      ((CFSG.QuasithinUnique.Setup.X6.isSylowTwoOf_iff_isSylowOf).mp hsylow)
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)

omit [Finite Ω] in
private theorem exists_mul_preimage_g45ic {M K G S : Subgroup Ω}
    (hMG : M ≤ G) (hKM : K ≤ M) (hKS : K ⊔ S = G)
    (hSK : S ≤ Subgroup.normalizer (K : Set Ω)) {y : Ω} (hy : y ∈ M) :
    ∃ k ∈ K, ∃ s ∈ S, k * s = y ∧ s ∈ M := by
  have hyG : y ∈ ((K ⊔ S : Subgroup Ω) : Set Ω) := hKS ▸ hMG hy
  rw [Subgroup.coe_mul_of_right_le_normalizer_left K S hSK] at hyG
  obtain ⟨k, hkK, s, hsS, hks⟩ := Set.mem_mul.mp hyG
  refine ⟨k, hkK, s, hsS, hks, ?_⟩
  rw [show s = k⁻¹ * y by rw [← hks]; group]
  exact M.mul_mem (M.inv_mem (hKM hkK)) hy

omit [Finite Ω] in
private theorem exists_action_mul_preimage_g45ic {W M G K S : Subgroup Ω}
    {hM : M ≤ Subgroup.normalizer (W : Set Ω)} {P : Subgroup (MulAut ↥W)}
    (hMG : M ≤ G) (hKM : K ≤ M) (hKS : K ⊔ S = G)
    (hSK : S ≤ Subgroup.normalizer (K : Set Ω))
    (hmemK : ∀ (k : Ω) (hk : k ∈ K), A4.actionOn W M hM ⟨k, hKM hk⟩ ∈ P)
    (hS2 : IsPGroup 2 S) {a : MulAut ↥W} (haA : a ∈ autOn M W) :
    ∃ (p b : MulAut ↥W) (n : ℕ), p ∈ P ∧ b ∈ autOn M W ∧ a = p * b ∧ b ^ 2 ^ n = 1 := by
  obtain ⟨y, hy⟩ := (A4.mem_autOn_iff hM).1 haA
  obtain ⟨k, hkK, s, hsS, hks, hsM⟩ := exists_mul_preimage_g45ic hMG hKM hKS hSK y.2
  have hkM : k ∈ M := hKM hkK
  have hy_eq : (y : ↥M) = ⟨k, hkM⟩ * ⟨s, hsM⟩ := by
    ext
    exact hks.symm
  obtain ⟨n, hn⟩ := IsPGroup.exists_pow_pow_eq_one hS2 (⟨s, hsS⟩ : ↥S)
  have hspow : s ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  refine ⟨A4.actionOn W M hM ⟨k, hkM⟩, A4.actionOn W M hM ⟨s, hsM⟩, n, ?_, ?_, ?_, ?_⟩
  · exact hmemK k hkK
  · exact (A4.mem_autOn_iff hM).2 ⟨⟨s, hsM⟩, rfl⟩
  · rw [← hy, hy_eq, map_mul]
  · rw [← map_pow, show (⟨s, hsM⟩ : ↥M) ^ 2 ^ n = 1 from Subtype.ext hspow, map_one]

private theorem autOn_inf_centralizer_le_of_sup_eq_g45ic
    (h : GomiThm45Counterexample c G S) {M : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    {P : Subgroup (MulAut ↥(gomiV M))} (hPM : P ≤ autOn M (gomiV M))
    (hPG : autOn G (gomiV M) ≤ Subgroup.normalizer (P : Set (MulAut ↥(gomiV M))))
    (hKS : preimage_g45ic M (gomiV_moduleSetting M).2 P ⊔ S = G) :
    autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) ≤ P := by
  let W := gomiV M
  have hM : M ≤ Subgroup.normalizer (W : Set Ω) := (gomiV_moduleSetting M).2
  let K : Subgroup Ω := preimage_g45ic M hM P
  have hKM : K ≤ M := preimage_g45ic_le P
  have hGW : G ≤ Subgroup.normalizer (W : Set Ω) :=
    le_normalizer_gomiV_of_le_normalizer hGM
  have hNK : G ≤ Subgroup.normalizer (K : Set Ω) := le_normalizer_preimage_g45ic hGW hGM hPG
  have hSK : S ≤ Subgroup.normalizer (K : Set Ω) := h.isSylowTwoOf.1.trans hNK
  have hOdd : Odd (Nat.card (autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) W)) :=
    odd_card_autOn_inf_centralizer h hMG hGM
  intro a ha
  have hodd : Odd (orderOf a) :=
    hOdd.of_dvd_nat (Subgroup.orderOf_dvd_natCard _ ha)
  have haA : a ∈ autOn M W := (AutOn.autOn_mono inf_le_left) ha
  obtain ⟨p, b, n, hpP, hbA, ha_decomp, hbpow⟩ :=
    exists_action_mul_preimage_g45ic hMG hKM hKS hSK
      (fun k hk => (mem_preimage_g45ic (M := M) (hM := hM) (hKM hk)).1 hk)
      h.isSylowTwoOf.2.1 haA
  have hpA : p ∈ autOn M W := hPM hpP
  have hPN : (P.subgroupOf (autOn M W)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mpr
      ((AutOn.autOn_mono hMG).trans hPG)
  have hoddA : Odd (orderOf (⟨a, haA⟩ : ↥(autOn M W))) := by
    rw [← Subgroup.orderOf_coe (⟨a, haA⟩ : ↥(autOn M W))]
    exact hodd
  have hxyeq : (⟨a, haA⟩ : ↥(autOn M W)) = ⟨p, hpA⟩ * ⟨b, hbA⟩ := Subtype.ext ha_decomp
  have hpPA : (⟨p, hpA⟩ : ↥(autOn M W)) ∈ P.subgroupOf (autOn M W) :=
    Subgroup.mem_subgroupOf.mpr hpP
  have hbpowA : (⟨b, hbA⟩ : ↥(autOn M W)) ^ 2 ^ n = 1 := Subtype.ext hbpow
  have hmemA : (⟨a, haA⟩ : ↥(autOn M W)) ∈ P.subgroupOf (autOn M W) :=
    @mem_of_odd_orderOf_of_mul_pow_two_g45ic (autOn M W) _ (P.subgroupOf (autOn M W)) hPN
      ⟨a, haA⟩ ⟨b, hbA⟩ ⟨p, hpA⟩ hoddA hpPA hxyeq n hbpowA
  exact hmemA

theorem autOn_inf_centralizer_le (h : GomiThm45Counterexample c G S) {M : Subgroup Ω}
    (hMG : M ≤ G) (hGM : G ≤ Subgroup.normalizer (M : Set Ω))
    {P : Subgroup (MulAut ↥(gomiV M))} (hPM : P ≤ autOn M (gomiV M))
    (hPG : autOn G (gomiV M) ≤ Subgroup.normalizer (P : Set (MulAut ↥(gomiV M))))
    (h2 : 2 ∣ Nat.card P) :
    autOn (M ⊓ Subgroup.centralizer (gomiV G : Set Ω)) (gomiV M) ≤ P :=
  autOn_inf_centralizer_le_of_sup_eq_g45ic h hMG hGM hPM hPG
    (sup_preimage_g45ic h hMG hGM hPM hPG h2)

end CFSG.GroupTheory.GomiThm45Counterexample
