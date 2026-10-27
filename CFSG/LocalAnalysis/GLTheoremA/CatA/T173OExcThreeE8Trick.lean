module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE8Data
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeE8Frame
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T173OExcThreeCoprime
public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10FBaseIso
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs119
public import CFSG.LocalAnalysis.GLTheoremA.S11.Inputs16
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsCE
public import CFSG.LocalAnalysis.GLTheoremA.S11.InputsElim

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T173O

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA
open CFSG.LocalAnalysis.GLTheoremA.T173 CFSG.LocalAnalysis.GLTheoremA.T173X
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.StandardType CFSG.StandardType.TableBExcTwo CFSG.StandardType.TableBExcTwoTB
open CFSG.StandardType.TableBExcTwoFusion
open CFSG.SeitzReduction.E8Pilot

section Generic

variable {G₀ : Type} [Group G₀]

theorem false_of_conj_mem_centralizer_stdLayer {p : ℕ} {A : Subgroup G₀} {d x n : G₀}
    (hd : IsStdElt p A d) (hx : stdLayer d ≤ Subgroup.centralizer ({x} : Set G₀))
    (hn : n * d = d * n) (hA : n * x * n⁻¹ ∈ A) (hnd : n * x * n⁻¹ ∉ Subgroup.zpowers d) :
    False := by
  have hn' : n⁻¹ * d = d * n⁻¹ := by
    calc n⁻¹ * d = n⁻¹ * (d * n) * n⁻¹ := by group
      _ = n⁻¹ * (n * d) * n⁻¹ := by rw [← hn]
      _ = d * n⁻¹ := by group
  have hmemn : n ∈ Subgroup.centralizer ({d} : Set G₀) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hn
  have hmeminv : n⁻¹ ∈ Subgroup.centralizer ({d} : Set G₀) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hn'
  have hcent : n * x * n⁻¹ ∈ Subgroup.centralizer (stdLayer d : Set G₀) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : n⁻¹ * s * n ∈ stdLayer d := by
      have hmap := map_conj_stdLayer_eq_of_mem_centralizer (d := d) hmeminv
      have hmem : (MulAut.conj n⁻¹) s ∈ (stdLayer d).map (MulAut.conj n⁻¹).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hs
      rw [hmap] at hmem
      simpa [MulAut.conj_apply] using hmem
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hx hs')
    calc s * (n * x * n⁻¹) = n * ((n⁻¹ * s * n) * x) * n⁻¹ := by group
      _ = n * (x * (n⁻¹ * s * n)) * n⁻¹ := by rw [hcomm]
      _ = (n * x * n⁻¹) * s := by group
  have hmemA : n * x * n⁻¹ ∈ A ⊓ Subgroup.centralizer (stdLayer d : Set G₀) :=
    Subgroup.mem_inf.mpr ⟨hA, hcent⟩
  rw [hd.2.2.2.2] at hmemA
  exact hnd hmemA

end Generic

section Frame


variable (K : Type) [Field K] [Finite K] [CharP K 2]

theorem exists_conj_tE_eq_of_torusWord (hK : Nat.card K = 2) (w : List (Fin Tag.E8.rank)) :
    ∃ n : ↥(adjointGroup .E8 K), ∀ u v : Fin 8 → ZMod 3,
      TableBExc.torusWord Tag.E8 3 w (e8FrameLambda u) = e8FrameLambda v →
        n * tE K frameE8 (Multiplicative.ofAdd u) * n⁻¹ =
          tE K frameE8 (Multiplicative.ofAdd v) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set L := FiniteField.Extension K 2 2 with hL
  obtain ⟨ω, hωo⟩ := TableBSymp.exists_orderOf_eq_of_dvd (K := L) (p := 3)
    (three_dvd_natCard_ext_sub_one hK)
  have hω3 : ω ^ 3 = 1 := hωo ▸ pow_orderOf_eq_one ω
  have hfull : ∀ a : Fin Tag.E8.rank → Lˣ,
      CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit Tag.E8 a ∈
        torusGroup Tag.E8 L :=
    TableBExc.full_of_E7_E8 (Or.inr rfl)
  set g := langElt frameE8 hωo with hg
  set m : adjointGroup .E8 L :=
    ⟨canonicalRep (coxeterSystem Tag.E8) L ((coxeterSystem Tag.E8).wordProd w),
      canonicalRep_mem_adjointGroup (coxeterSystem Tag.E8) L _⟩ with hm
  set D : (Fin Tag.E8.rank → ZMod 3) → adjointGroup .E8 L := fun s =>
    ⟨ExcFrames.frameDiag ω hω3 s,
      ExcFrames.frameDiag_mem_adjointGroup hfull ω hω3 s⟩ with hD
  have hDconj : ∀ s, m * D s * m⁻¹ = D (TableBExc.torusWord Tag.E8 3 w s) := by
    intro s
    have h := ExcFrames.canonicalRep_conj_frameDiag (τ := Tag.E8) (L := L) (p := 3) ω hω3
      ((coxeterSystem Tag.E8).wordProd w) s
    rw [TableBExc.torusWord_eq_torusAct TableBExc.Three.cartan_symm_E8]
    apply Subtype.ext
    exact h
  have hDtE : ∀ u, adjointMap .E8 (algebraMap K L) (tE K frameE8 (Multiplicative.ofAdd u)) =
      g * D (e8FrameLambda u) * g⁻¹ := by
    intro u
    have h := ExcFrameIso.adjointMap_tE_eq frameE8.symm_one frameE8 hωo hω3 hfull u
    rwa [frameCoordHom_frameE8_eq] at h
  obtain ⟨n, hn⟩ := exists_adjointMap_eq_of_frob (Or.inr rfl)
    (adjointMap_frob_conj_langElt hK frameE8 frameE8_reflections TableBExc.Three.cartan_symm_E8
      (TableBExc.isUnit_det_cartan_of_eq Nat.prime_three det_cartan_E8 (by norm_num))
      (TableBExc.card_torusPow_E8 (K := L) Nat.prime_three
        (three_dvd_natCard_ext_sub_one hK)) hωo
      (m := m) (CFSG.LieType.Chevalley.canonicalRep_mem_monomialSubgroup L
        ((coxeterSystem Tag.E8).wordProd w)))
  refine ⟨n, ?_⟩
  intro u v huv
  apply adjointMap_injective (algebraMap K L)
  calc
    adjointMap .E8 (algebraMap K L) (n * tE K frameE8 (Multiplicative.ofAdd u) * n⁻¹)
        = adjointMap .E8 (algebraMap K L) n *
            adjointMap .E8 (algebraMap K L) (tE K frameE8 (Multiplicative.ofAdd u)) *
            (adjointMap .E8 (algebraMap K L) n)⁻¹ := by rw [map_mul, map_mul, map_inv]
    _ = (g * m * g⁻¹) * (g * D (e8FrameLambda u) * g⁻¹) * (g * m * g⁻¹)⁻¹ := by
          rw [hn, hDtE u]
    _ = g * (m * D (e8FrameLambda u) * m⁻¹) * g⁻¹ := by group
    _ = g * D (e8FrameLambda v) * g⁻¹ := by rw [hDconj, huv]
    _ = adjointMap .E8 (algebraMap K L) (tE K frameE8 (Multiplicative.ofAdd v)) := (hDtE v).symm

private theorem exists_smul_of_mem_zpowers_tE {r c : Fin 8 → ZMod 3}
    (h : tE K frameE8 (Multiplicative.ofAdd c) ∈
      Subgroup.zpowers (tE K frameE8 (Multiplicative.ofAdd r))) :
    ∃ k : ZMod 3, c = k • r := by
  set d : adjointGroup .E8 K := tE K frameE8 (Multiplicative.ofAdd r) with hd
  have h' : tE K frameE8 (Multiplicative.ofAdd c) ∈ Subgroup.zpowers d := by rwa [hd]
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp h'
  have h3r : (3 : ℕ) • r = 0 := by
    funext i
    rw [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hd3 : d ^ 3 = 1 := by
    rw [hd, ← map_pow, ← ofAdd_nsmul, h3r, ofAdd_zero, map_one]
  have hmod : d ^ n = d ^ (n % 3) := by
    simpa using zpow_eq_zpow_emod' n hd3
  rw [hmod, hd] at hn
  rcases (by omega : n % 3 = 0 ∨ n % 3 = 1 ∨ n % 3 = 2) with h0 | h1 | h2
  · refine ⟨0, ?_⟩
    rw [h0, zpow_zero] at hn
    have h1' : tE K frameE8 (Multiplicative.ofAdd c) =
        tE K frameE8 (Multiplicative.ofAdd (0 : Fin 8 → ZMod 3)) := by
      rw [ofAdd_zero, map_one]
      exact hn.symm
    have hc : c = 0 :=
      Multiplicative.ofAdd.injective (tE_injective (K := K) frameE8 h1')
    rw [hc, zero_smul]
  · refine ⟨1, ?_⟩
    rw [h1, zpow_one] at hn
    have hc : c = r :=
      Multiplicative.ofAdd.injective (tE_injective (K := K) frameE8 hn.symm)
    rw [hc, one_smul]
  · refine ⟨2, ?_⟩
    rw [h2, zpow_two] at hn
    have hrr : tE K frameE8 (Multiplicative.ofAdd r) * tE K frameE8 (Multiplicative.ofAdd r) =
        tE K frameE8 (Multiplicative.ofAdd (r + r)) := by
      rw [← map_mul, ← ofAdd_add]
    have h1' : tE K frameE8 (Multiplicative.ofAdd c) =
        tE K frameE8 (Multiplicative.ofAdd (r + r)) := by
      rw [← hn]
      exact hrr
    have hc : c = r + r :=
      Multiplicative.ofAdd.injective (tE_injective (K := K) frameE8 h1')
    rw [hc, two_smul]

theorem false_of_isStdElt_of_mem_e8FrameTrickData (hK : Nat.card K = 2)
    {r : Fin 8 → ZMod 3} {w : List (Fin Tag.E8.rank)} {c : Fin 8 → ZMod 3}
    (hx : (r, w, c) ∈ e8FrameTrickData)
    (hd : IsStdElt 3 (e8FrameV K) (tE K frameE8 (Multiplicative.ofAdd r)))
    (hKD : stdLayer (tE K frameE8 (Multiplicative.ofAdd r)) ≤ e7Levi K) : False := by
  obtain ⟨hfix, hsend, -, hc0, hnc⟩ := e8FrameTrickData_spec (r, w, c) hx
  obtain ⟨n, hn⟩ := exists_conj_tE_eq_of_torusWord (K := K) hK w
  have hnd : n * tE K frameE8 (Multiplicative.ofAdd r) * n⁻¹ =
      tE K frameE8 (Multiplicative.ofAdd r) := hn r r hfix
  have hns : n * tE K frameE8 (Multiplicative.ofAdd (Pi.single 0 1)) * n⁻¹ =
      tE K frameE8 (Multiplicative.ofAdd c) := hn (Pi.single 0 1) c hsend
  have hmemV : tE K frameE8 (Multiplicative.ofAdd c) ∈ e8FrameV K :=
    (mem_e8FrameV_iff (K := K)).mpr ⟨c, hc0, rfl⟩
  have hnot : tE K frameE8 (Multiplicative.ofAdd c) ∉
      Subgroup.zpowers (tE K frameE8 (Multiplicative.ofAdd r)) := by
    intro hmem
    obtain ⟨k, hk⟩ := exists_smul_of_mem_zpowers_tE (K := K) hmem
    exact hnc k hk
  have hs0 : tE K frameE8 (Multiplicative.ofAdd (Pi.single (0 : Fin 8) 1)) =
      tGen K frameE8 0 := by
    rw [tE_single, tC_one]
  have hxle : stdLayer (tE K frameE8 (Multiplicative.ofAdd r)) ≤
      Subgroup.centralizer
        ({tE K frameE8 (Multiplicative.ofAdd (Pi.single 0 1))} : Set ↥(adjointGroup .E8 K)) := by
    rw [hs0]
    exact hKD.trans e7Levi_le_centralizer_tGen_zero
  have hA : n * tE K frameE8 (Multiplicative.ofAdd (Pi.single 0 1)) * n⁻¹ ∈ e8FrameV K := by
    rw [hns]
    exact hmemV
  have hncomm : n * tE K frameE8 (Multiplicative.ofAdd r) =
      tE K frameE8 (Multiplicative.ofAdd r) * n := by
    calc n * tE K frameE8 (Multiplicative.ofAdd r) =
        (n * tE K frameE8 (Multiplicative.ofAdd r) * n⁻¹) * n := by group
      _ = tE K frameE8 (Multiplicative.ofAdd r) * n := by rw [hnd]
  exact false_of_conj_mem_centralizer_stdLayer (p := 3) (A := e8FrameV K) hd hxle
    hncomm hA (by rw [hns]; exact hnot)

end Frame

end CFSG.LocalAnalysis.GLTheoremA.T173O

end
