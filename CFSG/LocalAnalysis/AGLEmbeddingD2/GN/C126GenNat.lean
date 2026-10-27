module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenFam
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.C126GenIndep
public import CFSG.Quasithin.Background.C126NatDMin

public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin B2F E2 CFSG.Quasithin.C126.Nat
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

structure NatCtxGen (H T M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (I : Finset (Subgroup (MulAut (IntMod V hV)))) : Prop where
  min : MinParabolic H T M
  charTwo : CharTwo H
  red : IsTwoReducedIn H V
  hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)
  kj : twoResidual H ≤ thompsonJ H
  jeq : autI hV (thompsonJ H) = ⨆ L ∈ I, L
  comm : ∀ L ∈ I, ∀ L' ∈ I, L ≠ L' → ∀ a ∈ L, ∀ b ∈ L', a * b = b * a
  ind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥
  trans : ∀ L ∈ I, ∀ L' ∈ I, ∃ t ∈ autI hV T, B1.conjAut t L = L'
  nat : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n
  sbj : autI hV (baum T) = autI hV (thompsonJ T)
  sylJ : IsSylowTwoOf (autI hV (thompsonJ T)) (autI hV (thompsonJ H))
  syl : IsSylowTwoOf (baum T) (twoResidual H ⊔ baum T)

omit [Finite G] in
theorem natCtxGen_of_fam {H T M V : Subgroup G} {hV : IsElemAbelian 2 V}
    {I : Finset (Subgroup (MulAut (IntMod V hV)))}
    (hmin : MinParabolic H T M) (hF : CharTwo H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hKJ : twoResidual H ≤ thompsonJ H)
    (hFam : E23FamGen H T V hV I)
    (hn2 : ∀ L ∈ I, ∃ n : ℕ, 2 ≤ n ∧ IsL2Natural L (fixV (autI hV (twoResidual H))) n) :
    NatCtxGen H T M V hV I := by
  obtain ⟨-, hJeq, hcomm, htrans, -, h2, -⟩ := hFam
  have hind : ∀ L ∈ I, L ⊓ ⨆ L' ∈ I, ⨆ (_ : L' ≠ L), L' = ⊥ := fun L hL =>
    inf_biSup_eq_bot_of_isL2Natural hcomm (fun L hL => (hn2 L hL).imp fun n h => h.2) hL
  obtain ⟨hsb, hsylJ, hsyl⟩ := h2 fun L hL => (hn2 L hL).imp fun n h => h.2
  exact ⟨hmin, hF, hred, hJ, hKJ, hJeq, hcomm, hind, htrans, hn2, hsb, hsylJ, hsyl⟩

omit [Finite G] in
theorem exists_natCtxGen {H T M V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hmin : MinParabolic H T M) (hF : CharTwo H) (hred : IsTwoReducedIn H V)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (V : Set G)) (hNat : NatCaseGen H T V hV) :
    ∃ I, NatCtxGen H T M V hV I := by
  obtain ⟨hKJ, I, hFam, hn2⟩ := hNat
  exact ⟨I, natCtxGen_of_fam hmin hF hred hJ hKJ hFam hn2⟩

namespace NatCtxGen

variable {H T M V : Subgroup G} {hV : IsElemAbelian 2 V}
  {I : Finset (Subgroup (MulAut (IntMod V hV)))} (c : NatCtxGen H T M V hV I)

omit [Finite G] in
include c in
theorem hHN : H ≤ Subgroup.normalizer (V : Set G) := c.red.2.1

omit [Finite G] in
include c in
theorem not_le_centralizer : ¬ H ≤ Subgroup.centralizer (V : Set G) := fun hle =>
  c.hJ ((B6.thompsonJ_le T).trans (c.min.isSylow.1.trans hle))

include c in
theorem cent_le_M : H ⊓ Subgroup.centralizer (V : Set G) ≤ M :=
  (c.min.inf_centralizer_le_kerIn c.red c.not_le_centralizer).trans kerIn_le

omit [Finite G] in
include c in
theorem sylow_star : IsSylowTwoOf (autI hV (baum T)) (⨆ L ∈ I, L) := by
  have h := c.sylJ
  rw [c.jeq, ← c.sbj] at h
  exact h

include c in
theorem rho_le {P : Subgroup G} (hPK : P ≤ twoResidual H ⊔ baum T) :
    autI hV P ≤ ⨆ L ∈ I, L := by
  have hTH := c.min.isSylow.1
  have hSN : baum T ≤ Subgroup.normalizer (V : Set G) :=
    (inf_le_left.trans hTH).trans c.hHN
  have hKN : twoResidual H ≤ Subgroup.normalizer (V : Set G) := (twoResidual_le H).trans c.hHN
  calc autI hV P ≤ autI hV (twoResidual H ⊔ baum T) := autI_mono hV hPK
    _ = autI hV (twoResidual H) ⊔ autI hV (baum T) := autI_sup hV hKN hSN
    _ ≤ autI hV (thompsonJ H) := by
      refine sup_le (autI_mono hV c.kj) ?_
      rw [c.sbj]
      exact autI_mono hV (B6.thompsonJ_le_of_sylow c.min.isSylow)
    _ = ⨆ L ∈ I, L := c.jeq

include c in
theorem not_le_rho_M : ∀ L ∈ I, ¬ L ≤ autI hV M := by
  intro L hL hLM
  have hall : ⨆ L' ∈ I, L' ≤ autI hV M := by
    refine iSup₂_le fun L' hL' => ?_
    obtain ⟨t, ht, hLt⟩ := c.trans L hL L' hL'
    rw [← hLt]
    intro x hx
    have h1 := hLM (B1.mem_conjAut.1 hx)
    have htM : t ∈ autI hV M := autI_mono hV c.min.le ht
    have h2 : t * (t⁻¹ * x * t) * t⁻¹ ∈ autI hV M :=
      (autI hV M).mul_mem ((autI hV M).mul_mem htM h1) ((autI hV M).inv_mem htM)
    simpa [mul_assoc] using h2
  have hKM : twoResidual H ≤ M := by
    intro k hk
    have hkH : k ∈ H := twoResidual_le H hk
    have hmem : convI hV ⟨k, c.hHN hkH⟩ ∈ autI hV M :=
      hall (c.jeq ▸ autI_mono hV c.kj (convI_mem_autI hV hk (c.hHN hkH)))
    obtain ⟨m, hm, hconv⟩ := (mem_autI hV).1 hmem
    have h1 : convI hV (⟨k, c.hHN hkH⟩ * m⁻¹) = 1 := by rw [map_mul, map_inv, hconv, mul_inv_cancel]
    have h2 : k * (m : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
    have hmH : (m : G) ∈ H := c.min.maximal.1.le (hm : (m : G) ∈ M)
    have h3 : k * (m : G)⁻¹ ∈ M :=
      c.cent_le_M ⟨H.mul_mem hkH (H.inv_mem hmH), h2⟩
    have := M.mul_mem h3 hm
    simpa using this
  have hH : H ≤ M := by
    rw [← sup_twoResidual_eq c.min.isSylow]
    exact sup_le c.min.le hKM
  exact absurd (lt_of_le_of_lt hH c.min.maximal.1) (lt_irrefl _)

omit [Finite G] in
include c in
theorem iSup_le_normalizer {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I) :
    (⨆ L' ∈ I, L') ≤ Subgroup.normalizer (L : Set (MulAut (IntMod V hV))) := by
  refine iSup₂_le fun L' hL' => ?_
  by_cases h : L' = L
  · rw [h]
    exact Subgroup.le_normalizer
  · exact le_normalizer_of_commuting (c.comm L hL L' hL' (Ne.symm h))

include c in
theorem le_normalizer_star {X : Subgroup (MulAut (IntMod V hV))} (hX : X ≤ ⨆ L ∈ I, L)
    (hSX : autI hV (baum T) ≤ X) (hno : ∀ L ∈ I, ¬ L ≤ X) :
    X ≤ Subgroup.normalizer
      ((autI hV (baum T) : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV))) := by
  have hS := c.sylow_star
  refine le_normalizer_of_factors c.comm c.ind hS hX hSX (fun L hL Z hZL hSZ => ?_) hno
  obtain ⟨n, -, hnat⟩ := c.nat L hL
  obtain ⟨hn, F, iF, iFin, hF, ⟨e⟩⟩ := NatCtx.exists_equiv_sl2 hnat
  have hSyl : IsSylowTwoOf (autI hV (baum T) ⊓ L) L :=
    B6.isSylowTwoOf_inf_normal hS (le_iSup₂_of_le (f := fun (K : Subgroup (MulAut (IntMod V hV)))
      (_ : K ∈ I) => K) L hL le_rfl) (c.iSup_le_normalizer hL)
  exact sylow_dichotomy_of_equiv_sl2 hn hF e hSyl hZL hSZ

include c in
theorem le_M_of_rho_le_normalizer {P : Subgroup G} (hPH : P ≤ H) (hSP : baum T ≤ P)
    (hmP : MinParabolic P (baum T) (P ⊓ M))
    (hρ : autI hV P ≤ Subgroup.normalizer
      ((autI hV (baum T) : Subgroup (MulAut (IntMod V hV))) : Set (MulAut (IntMod V hV)))) :
    P ≤ M := by
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPH.trans c.hHN
  have hSS : autI hV (baum T) ≤ autI hV P := autI_mono hV hSP
  set SC : Subgroup G := preI hV P hPN (autI hV (baum T)) with hSC
  have hSSC : baum T ≤ SC := fun s hs =>
    (mem_preI hV).2 ⟨hSP hs, convI_mem_autI hV hs (hPN (hSP hs))⟩
  have hSCP : SC ≤ P := preI_le hV
  have hsyl : IsSylowTwoOf (baum T) SC := A4.isSylowTwoOf_mono hmP.isSylow hSSC hSCP
  have hSCM : SC ≤ M := by
    intro n hn
    obtain ⟨hnP, hnS⟩ := (mem_preI hV).1 hn
    obtain ⟨s, hs, hsn⟩ := (mem_autI hV).1 hnS
    have h1 : convI hV (⟨n, hPN hnP⟩ * s⁻¹) = 1 := by
      rw [map_mul, map_inv, hsn]
      exact mul_inv_cancel _
    have h2 : n * (s : G)⁻¹ ∈ Subgroup.centralizer (V : Set G) := (convI_eq_one_iff hV _).1 h1
    have hsT : (s : G) ∈ T := hs.1
    have hsH : (s : G) ∈ H := c.min.isSylow.1 hsT
    have h3 : n * (s : G)⁻¹ ∈ M := c.cent_le_M ⟨H.mul_mem (hPH hnP) (H.inv_mem hsH), h2⟩
    have := M.mul_mem h3 (c.min.le hsT)
    simpa using this
  have hkey : ∀ q ∈ P, ∀ y ∈ SC, q * y * q⁻¹ ∈ SC := by
    intro q hq y hy
    obtain ⟨hyP, hyS⟩ := (mem_preI hV).1 hy
    have hqyP : q * y * q⁻¹ ∈ P := P.mul_mem (P.mul_mem hq hyP) (P.inv_mem hq)
    refine (mem_preI hV).2 ⟨hqyP, ?_⟩
    have h1 : convHom hV P hPN ⟨q * y * q⁻¹, hqyP⟩ =
        convHom hV P hPN ⟨q, hq⟩ * convHom hV P hPN ⟨y, hyP⟩ * (convHom hV P hPN ⟨q, hq⟩)⁻¹ := by
      rw [← map_inv, ← map_mul, ← map_mul]
      rfl
    rw [h1]
    have hqρ : convHom hV P hPN ⟨q, hq⟩ ∈ Subgroup.normalizer
        ((autI hV (baum T) : Subgroup (MulAut (IntMod V hV))) :
          Set (MulAut (IntMod V hV))) :=
      hρ (convI_mem_autI hV hq (hPN hq))
    exact (Subgroup.mem_normalizer_iff.1 hqρ _).1 hyS
  intro p hp
  have hpSC : p ∈ Subgroup.normalizer (SC : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    refine ⟨hkey p hp y, fun hy => ?_⟩
    have := hkey p⁻¹ (P.inv_mem hp) _ hy
    simpa [mul_assoc] using this
  obtain ⟨n, hn, m, hm, rfl⟩ := exists_mul_normalizer_of_sylow hsyl hpSC
  have hmPm : m ∈ P := by
    have := P.mul_mem (P.inv_mem (hSCP hn)) hp
    simpa using this
  have hmM : m ∈ M := (hmP.inf_normalizer_le ⟨hmPm, hm⟩).2
  exact M.mul_mem (hSCM hn) hmM


include c in
theorem exists_factor_le_rho {P : Subgroup G} (hPH : P ≤ H) (hSP : baum T ≤ P)
    (hPK : P ≤ twoResidual H ⊔ baum T) (hPM : ¬ P ≤ M)
    (hmP : MinParabolic P (baum T) (P ⊓ M)) : ∃ L ∈ I, L ≤ autI hV P := by
  by_contra hno
  push Not at hno
  exact hPM (c.le_M_of_rho_le_normalizer hPH hSP hmP
    (c.le_normalizer_star (c.rho_le hPK) (autI_mono hV hSP) hno))

include c in
theorem rho_eq {P : Subgroup G} (hPH : P ≤ H) (hSP : baum T ≤ P)
    (hmP : MinParabolic P (baum T) (P ⊓ M)) {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I)
    (hLP : L ≤ autI hV P) : autI hV P = L ⊔ autI hV (baum T) := by
  have hPN : P ≤ Subgroup.normalizer (V : Set G) := hPH.trans c.hHN
  have hSS : autI hV (baum T) ≤ autI hV P := autI_mono hV hSP
  have hB : L ⊔ autI hV (baum T) ≤ autI hV P := sup_le hLP hSS
  have hP'P : preI hV P hPN (L ⊔ autI hV (baum T)) ≤ P := preI_le hV
  have hSP' : baum T ≤ preI hV P hPN (L ⊔ autI hV (baum T)) := fun s hs =>
    (mem_preI hV).2 ⟨hSP hs, Subgroup.mem_sup_right (convI_mem_autI hV hs (hPN (hSP hs)))⟩
  have hrho : autI hV (preI hV P hPN (L ⊔ autI hV (baum T))) = L ⊔ autI hV (baum T) :=
    autI_preI hV hB
  have hP'M : ¬ preI hV P hPN (L ⊔ autI hV (baum T)) ≤ M := fun h =>
    c.not_le_rho_M L hL (le_sup_left.trans (hrho ▸ autI_mono hV h))
  have hP'eq : preI hV P hPN (L ⊔ autI hV (baum T)) = P := by
    by_contra hne
    exact hP'M ((hmP.le_of_lt hSP' (lt_of_le_of_ne hP'P hne)).trans inf_le_right)
  rw [← hrho, hP'eq]

include c in
theorem rho_twoResidual_eq {P : Subgroup G} (hPN : P ≤ Subgroup.normalizer (V : Set G))
    {L : Subgroup (MulAut (IntMod V hV))} (hL : L ∈ I)
    (hρ : autI hV P = L ⊔ autI hV (baum T)) : autI hV (twoResidual P) = L := by
  obtain ⟨n, hn, hnat⟩ := c.nat L hL
  obtain ⟨hn1, F, iF, iFin, hF, ⟨e⟩⟩ := NatCtx.exists_equiv_sl2 hnat
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hperf : ⁅L, L⁆ = L := commutator_eq_of_equiv_sl2 h4 e
  have hS := c.sylow_star
  rw [autI_twoResidual_eq hV hPN, hρ]
  exact twoResidual_sup_eq_of_perfect hperf hS.2.1
    (fun x hx => c.iSup_le_normalizer hL (hS.1 hx))

end NatCtxGen

end CFSG.AGLEmbeddingD2.GN
