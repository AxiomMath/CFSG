module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenNat
public import CFSG.Quasithin.Background.C126NatDComm

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2 CFSG.Quasithin.C126.Nat
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace NatCtxGen

variable {H T M V : Subgroup G} {hV : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hV)))} (c : NatCtxGen H T M V hV I)

include c in
theorem le_normalizer_KS :
    H ≤ Subgroup.normalizer ((twoResidual H ⊔ baum T : Subgroup G) : Set G) := by
  have hTbaum : T ≤ Subgroup.normalizer (baum T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hTn : T ≤ Subgroup.normalizer ((twoResidual H ⊔ baum T : Subgroup G) : Set G) :=
    fun t ht => C1.mem_normalizer_sup (le_normalizer_twoResidual H (c.min.isSylow.1 ht))
      (hTbaum ht)
  have hKn : twoResidual H ≤ Subgroup.normalizer ((twoResidual H ⊔ baum T : Subgroup G) : Set G) :=
    le_sup_left.trans Subgroup.le_normalizer
  exact (sup_twoResidual_eq c.min.isSylow).symm.le.trans (sup_le hTn hKn)

omit [Finite G] in
include c in
theorem KS_le_normalizer_K :
    twoResidual H ⊔ baum T ≤ Subgroup.normalizer (twoResidual H : Set G) :=
  sup_le Subgroup.le_normalizer fun _ hx =>
    le_normalizer_twoResidual H ((inf_le_left.trans c.min.isSylow.1) hx)

include c in
theorem twoResidual_le_K {W : Subgroup G} (hW : W ≤ twoResidual H ⊔ baum T) :
    twoResidual W ≤ twoResidual H := by
  have hKSnK := c.KS_le_normalizer_K
  have hN : W ≤ Subgroup.normalizer ((W ⊓ twoResidual H : Subgroup G) : Set G) := fun x hx =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hKSnK (hW hx)⟩
  have h2 : ∀ y ∈ W, ∃ k : ℕ, y ^ 2 ^ k ∈ W ⊓ twoResidual H := fun y hy => by
    obtain ⟨k, hk⟩ := B6.isTwoQuotient_of_sup_eq c.syl.2.1 hKSnK (sup_comm _ _) y (hW hy)
    exact ⟨k, W.pow_mem hy _, hk⟩
  exact (twoResidual_le_of_isTwoQuotient inf_le_left hN h2).trans inf_le_right

include c in
theorem kerK_le_baum (hRF : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ baum T := by
  have hSH : baum T ≤ H := inf_le_left.trans c.min.isSylow.1
  have hKSH : twoResidual H ⊔ baum T ≤ H := sup_le (twoResidual_le H) hSH
  intro x hx
  have hxO : x ∈ pCoreOf 2 H := hRF hx
  have hxKS : x ∈ twoResidual H ⊔ baum T := Subgroup.mem_sup_left hx.1
  have hnorm : twoResidual H ⊔ baum T ≤
      Subgroup.normalizer ((pCoreOf 2 H ⊓ (twoResidual H ⊔ baum T) : Subgroup G) : Set G) :=
    fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKSH hg), Subgroup.le_normalizer hg⟩
  exact B6.pCoreOf_two_le_of_isSylowTwoOf c.syl
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right hnorm
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_left) ⟨hxO, hxKS⟩)

include c in
theorem isSubnormal_K1 (hRF : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H)
    {P : Subgroup G} (hSP : baum T ≤ P) (hPK : P ≤ twoResidual H ⊔ baum T)
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) (hρ : autI hV (twoResidual P) = L)
    (hshort : ∀ (N : Subgroup ↥(twoResidual P)) [N.Normal],
      IsPGroup 2 (↥(twoResidual P) ⧸ N) → N = ⊤) :
    ((twoResidual P).subgroupOf H).IsSubnormal := by
  have hHN := c.hHN
  have hSH : baum T ≤ H := inf_le_left.trans c.min.isSylow.1
  have hKSH : twoResidual H ⊔ baum T ≤ H := sup_le (twoResidual_le H) hSH
  have hKSN : twoResidual H ⊔ baum T ≤ Subgroup.normalizer (V : Set G) := hKSH.trans hHN
  have hρKS : autI hV (twoResidual H ⊔ baum T) ≤ Subgroup.normalizer (L : Set _) :=
    (c.rho_le le_rfl).trans (c.iSup_le_normalizer hL)
  set W : Subgroup G := preI hV (twoResidual H ⊔ baum T) hKSN L with hW
  have hWKS : W ≤ twoResidual H ⊔ baum T := preI_le hV
  have hKW : twoResidual P ≤ W := fun x hx => (mem_preI hV).2
    ⟨hPK (twoResidual_le P hx), hρ ▸ convI_mem_autI hV hx (hKSN (hPK (twoResidual_le P hx)))⟩
  have hWnorm : twoResidual H ⊔ baum T ≤ Subgroup.normalizer (W : Set G) := fun g hg => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨fun hy => conj_mem_preI hV hKSN hρKS hg hy, fun hy => ?_⟩
    have := conj_mem_preI hV hKSN hρKS ((twoResidual H ⊔ baum T).inv_mem hg) hy
    simpa [mul_assoc] using this
  set B : Subgroup G := twoResidual W with hB
  have hKB : twoResidual P ≤ B := le_twoResidual_of_noTwoQuotient hKW hshort
  have hBK : B ≤ twoResidual H := c.twoResidual_le_K hWKS
  have hS2 : IsPGroup 2 ↥(baum T) := c.min.isSylow.2.1.to_le inf_le_left
  have hdec : ∀ b ∈ B, ∃ k ∈ twoResidual P, ∃ r ∈ baum T ⊓ B, b = k * r := by
    intro b hb
    obtain ⟨hbKS, hbL⟩ := (mem_preI hV).1 (twoResidual_le W hb)
    have hbL' : convI hV ⟨b, hKSN hbKS⟩ ∈ autI hV (twoResidual P) := by
      rw [hρ]
      exact hbL
    obtain ⟨k, hk, hkb⟩ := (mem_autI hV).1 hbL'
    have h1 : convI hV (k⁻¹ * ⟨b, hKSN hbKS⟩) = 1 := by
      rw [map_mul, map_inv, ← hkb, inv_mul_cancel]
    have h2 : (k : G)⁻¹ * b ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
    have hrB : (k : G)⁻¹ * b ∈ B := B.mul_mem (B.inv_mem (hKB hk)) hb
    exact ⟨k, hk, (k : G)⁻¹ * b, ⟨c.kerK_le_baum hRF ⟨hBK hrB, h2⟩, hrB⟩, by group⟩
  have hBnorm : B ≤ Subgroup.normalizer (twoResidual P : Set G) := by
    intro b hb
    obtain ⟨k, hk, r, hr, rfl⟩ := hdec b hb
    exact Subgroup.mul_mem _ (Subgroup.le_normalizer hk)
      (le_normalizer_twoResidual P (hSP hr.1))
  have hsup : (baum T ⊓ B) ⊔ twoResidual P = B := by
    apply le_antisymm
    · exact sup_le inf_le_right hKB
    · intro b hb
      obtain ⟨k, hk, r, hr, rfl⟩ := hdec b hb
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hk) (Subgroup.mem_sup_left hr)
  have h2q := B6.isTwoQuotient_of_sup_eq (hS2.to_le (inf_le_left : baum T ⊓ B ≤ baum T))
    hBnorm hsup
  have hBleK : B ≤ twoResidual P := by
    have := twoResidual_le_of_isTwoQuotient hKB hBnorm h2q
    rwa [hB, CFSG.Quasithin.C126.Nat.twoResidual_twoResidual] at this
  have hBeq : B = twoResidual P := le_antisymm hBleK hKB
  have hBKS : B ≤ twoResidual H ⊔ baum T := hBK.trans le_sup_left
  have hBn : twoResidual H ⊔ baum T ≤ Subgroup.normalizer (B : Set G) := fun x hx =>
    mem_normalizer_twoResidual (hWnorm hx)
  have hBnormal : (B.subgroupOf (twoResidual H ⊔ baum T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hBKS).2 hBn
  have hKSnormal : ((twoResidual H ⊔ baum T).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKSH).2 c.le_normalizer_KS
  rw [← hBeq]
  exact C1Pack.isSubnormal_subgroupOf_trans' hBKS hKSH hBnormal.isSubnormal
    hKSnormal.isSubnormal

include c in
theorem commutator_star_eq {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    ⁅L, autI hV (baum T)⁆ = L := by
  obtain ⟨n, hn2, hnat⟩ := c.nat L hL
  obtain ⟨hn, F, iF, iFin, hF, ⟨e⟩⟩ := NatCtx.exists_equiv_sl2 hnat
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hchar : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn hF
  have hLle : L ≤ ⨆ L' ∈ I, L' := le_iSup₂_of_le L hL le_rfl
  have hnorm := c.iSup_le_normalizer hL
  have hS := c.sylow_star
  have hSyl : IsSylowTwoOf (autI hV (baum T) ⊓ L) L := B6.isSylowTwoOf_inf_normal hS hLle hnorm
  have hne : autI hV (baum T) ⊓ L ≠ ⊥ := fun h0 => by
    have h1 := card_sylow_of_equiv_sl2 hn hF e hSyl
    rw [h0, Subgroup.card_bot] at h1
    have : 2 ≤ 2 ^ n := Nat.le_self_pow (by omega) 2
    omega
  have h1 := commutator_eq_of_ne_bot h4 e inf_le_right hne
  have hSn : autI hV (baum T) ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hV))) :=
    fun x hx => hnorm (hS.1 hx)
  refine le_antisymm (commutator_le_left_of_le_normalizer hSn) ?_
  calc L = ⁅L, autI hV (baum T) ⊓ L⁆ := h1.symm
    _ ≤ ⁅L, autI hV (baum T)⁆ := Subgroup.commutator_mono le_rfl inf_le_left

include c in
theorem commutator_K1_eq (hRF : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H)
    {P : Subgroup G} (hSP : baum T ≤ P) (hPK : P ≤ twoResidual H ⊔ baum T)
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) (hρ : autI hV (twoResidual P) = L) :
    ⁅twoResidual P, thompsonJ T⁆ = twoResidual P := by
  have hSH : baum T ≤ H := inf_le_left.trans c.min.isSylow.1
  have hKSH : twoResidual H ⊔ baum T ≤ H := sup_le (twoResidual_le H) hSH
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := (hPK.trans hKSH).trans c.hHN
  have hJP : thompsonJ T ≤ P := (B6.thompsonJ_le_baum T).trans hSP
  have hK1P : twoResidual P ≤ P := twoResidual_le P
  have hJn : thompsonJ T ≤ Subgroup.normalizer (twoResidual P : Set G) := fun j hj =>
    le_normalizer_twoResidual P (hJP hj)
  set K₁ : Subgroup G := twoResidual P with hK₁
  set X : Subgroup G := ⁅K₁, thompsonJ T⁆ with hX
  have hXK : X ≤ K₁ := commutator_le_left_of_le_normalizer hJn
  have hKX : K₁ ≤ Subgroup.normalizer (X : Set G) := le_normalizer_commutator_left K₁ _
  have hρX : autI hV X = L := by
    rw [hX, autI_commutator hV (hK1P.trans hPN) (hJP.trans hPN), hρ, ← c.sbj]
    exact c.commutator_star_eq hL
  have hKC : K₁ ⊓ Subgroup.centralizer (V : Set G) ≤ baum T := fun x hx =>
    c.kerK_le_baum hRF ⟨c.twoResidual_le_K hPK hx.1, hx.2⟩
  have hdec : ∀ k ∈ K₁, ∃ x ∈ X, ∃ r ∈ baum T ⊓ K₁, k = x * r := by
    intro k hk
    have hkN : k ∈ Subgroup.normalizer (V : Set G) := hPN (hK1P hk)
    have hmem : convI hV ⟨k, hkN⟩ ∈ autI hV X := by
      rw [hρX, ← hρ]
      exact convI_mem_autI hV hk hkN
    obtain ⟨x, hx, hxk⟩ := (mem_autI hV).1 hmem
    have h1 : convI hV (x⁻¹ * ⟨k, hkN⟩) = 1 := by
      rw [map_mul, map_inv, hxk, inv_mul_cancel]
    have h2 : (x : G)⁻¹ * k ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
    have hrK : (x : G)⁻¹ * k ∈ K₁ := K₁.mul_mem (K₁.inv_mem (hXK hx)) hk
    exact ⟨x, hx, (x : G)⁻¹ * k, ⟨hKC ⟨hrK, h2⟩, hrK⟩, by group⟩
  have hsup : (baum T ⊓ K₁) ⊔ X = K₁ := by
    apply le_antisymm
    · exact sup_le inf_le_right hXK
    · intro k hk
      obtain ⟨x, hx, r, hr, rfl⟩ := hdec k hk
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hx) (Subgroup.mem_sup_left hr)
  have hS2 : IsPGroup 2 ↥(baum T) := c.min.isSylow.2.1.to_le inf_le_left
  have h2q := B6.isTwoQuotient_of_sup_eq (hS2.to_le (inf_le_left : baum T ⊓ K₁ ≤ baum T)) hKX hsup
  have h3 := twoResidual_le_of_isTwoQuotient hXK hKX h2q
  rw [hK₁, CFSG.Quasithin.C126.Nat.twoResidual_twoResidual] at h3
  exact le_antisymm hXK h3

end NatCtxGen

theorem oneBlockGen_of_block {H T M V P : Subgroup G} {hV : IsElemAbelian 2 V}
    (hmin : MinParabolic H T M) (hF : CharTwo H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hNat : NatCaseGen H T V hV)
    (hRF : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H)
    (hSP : baum T ≤ P) (hPK : P ≤ twoResidual H ⊔ baum T) (hPM : ¬ P ≤ M) (hPT : P ⊔ T = H)
    (hMinP : MinParabolic P (baum T) (P ⊓ M)) (hBlk : IsL2OrA3Block P (twoResidual P)) :
    OneBlockGen H T := by
  obtain ⟨I, c⟩ := exists_natCtxGen hmin hF hred hJ hNat
  have hTH : T ≤ H := hmin.isSylow.1
  have hSH : baum T ≤ H := inf_le_left.trans hTH
  have hPH : P ≤ H := hPK.trans (sup_le (twoResidual_le H) hSH)
  obtain ⟨L, hL, hLP⟩ := c.exists_factor_le_rho hPH hSP hPK hPM hMinP
  have hρ := c.rho_twoResidual_eq (hPH.trans c.hHN) hL (c.rho_eq hPH hSP hMinP hL hLP)
  have hKH : twoResidual P ≤ H := (twoResidual_le P).trans hPH
  have hK1 : twoResidual P ≤ conjClosure (twoResidual P) T := fun z hz => by
    simpa using mem_conjClosure T.one_mem hz
  refine ⟨twoResidual P, ⟨⟨hBlk.1.1, hKH, c.isSubnormal_K1 hRF hSP hPK hL hρ hBlk.1.1.1⟩,
    hBlk.2.elim Or.inl fun h => Or.inr ⟨3, by decide, le_rfl, h⟩⟩,
    c.commutator_K1_eq hRF hSP hPK hL hρ,
    le_antisymm ?_ (sup_le hTH (conjClosure_le fun h hh z hz => ?_))⟩
  · have hP : baum T ⊔ twoResidual P = P := sup_twoResidual_eq hMinP.isSylow
    calc H = P ⊔ T := hPT.symm
      _ ≤ T ⊔ conjClosure (twoResidual P) T := sup_le (hP.symm.le.trans (sup_le
          (inf_le_left.trans le_sup_left) (hK1.trans le_sup_right))) le_sup_left
  · exact H.mul_mem (H.mul_mem (hTH hh) (hKH hz)) (H.inv_mem (hTH hh))

end CFSG.AGLEmbeddingD2.GN
