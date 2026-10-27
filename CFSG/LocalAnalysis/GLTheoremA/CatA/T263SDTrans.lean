module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDCore
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I142MThree
public import CFSG.LocalAnalysis.GLTheoremA.CatA.T263SDLift

public section

namespace CFSG.LocalAnalysis.GLTheoremA.T263.SD

open CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremB
open CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.S10
open CFSG.LocalAnalysis.GLTheoremA.T263 CFSG.LocalAnalysis.GLTheoremA.T263.DX
open CFSG.LocalAnalysis.GLTheoremA.KD264Lie
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup mem_fixSubgroup)
open scoped commutatorElement

variable {Ω : Type} [Group Ω] [Finite Ω]

theorem sdCore_of_famSel (hChev : CFSG.LocalAnalysis.GLTheoremA.I142M.Three.ChevCompTypes)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {S B B₀ T' : Subgroup Ω} {x : Ω}
    (hSn : S.Normal) (hSq : CFSG.Open.IsQuasisimple ↥S) (hSp : GLAPPrimeCore p ↥S = ⊥)
    (hSc : IsChevSimple 2 (↥S ⧸ Subgroup.center ↥S)) (hBel : IsElemAbelian p B) (hB₀B : B₀ ≤ B)
    (hxB₀ : x ∈ B₀) (hxC : x ∉ Subgroup.centralizer (S : Set Ω))
    (hT'2 : IsPGroup 2 ↥T') (hT'S : T' ≤ S) (hBT' : B ≤ Subgroup.normalizer (T' : Set Ω))
    (hS₁ : (⁅B₀, T' ⊓ Subgroup.centralizer ({x} : Set Ω)⁆ : Subgroup Ω) ≠ ⊥)
    {P : Type} [Group P] [Finite P] (θ : ↥S ⧸ Subgroup.center ↥S ≃* P) {inn : MulAut P → Prop}
    (hinn : ∀ b : ↥B, (b : Ω) ∈ B₀ → inn (kd264Rho (sd_hBN hSn B) θ b))
    (hF : FamSel p P inn) :
    ∃ J : Subgroup Ω, SDCore p S B₀ T' x J := by
  classical
  have hBN : B ≤ Subgroup.normalizer (S : Set Ω) := sd_hBN hSn B
  have hperf : Group.IsPerfect ↥S := Group.isPerfect_def.mpr hSq.1
  have hxB : x ∈ B := hB₀B hxB₀
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb => isElemAbelian_commute hBel ha hb
  set ρ : ↥B →* MulAut P := kd264Rho hBN θ with hρ
  set σ : ↥S →* P := sdσ θ with hσ
  have hσs : Function.Surjective σ := sdσ_surjective θ
  have hσker : σ.ker ≤ Subgroup.center ↥S := sdσ_ker_le θ
  let xB : ↥B := ⟨x, hxB⟩
  let α : MulAut ↥S := CFSG.normalizerConjAutOfMem S B hBN xB
  set u : MulAut P := ρ xB with hu
  have hαβ : ∀ k : ↥S, σ (α k) = u (σ k) := fun k => (sd_rho_apply hBN θ xB k).symm
  have hup : u ^ p = 1 := by
    rw [hu, ← map_pow]
    have : xB ^ p = 1 := Subtype.ext (by simpa using hBel.2 x hxB)
    rw [this, map_one]
  have hu1 : u ≠ 1 := by
    intro h
    have hmem : xB ∈ (kd264Rho hBN θ).ker := h
    rw [ker_kd264Rho hperf hBN θ, Subgroup.mem_subgroupOf] at hmem
    exact hxC (Subgroup.mem_inf.1 hmem).2
  have huinn : inn u := hinn xB hxB₀
  set 𝔹 : Subgroup (MulAut P) := (B₀.subgroupOf B).map ρ with h𝔹
  have h𝔹mem : ∀ b ∈ 𝔹, ∃ β : ↥B, (β : Ω) ∈ B₀ ∧ b = ρ β := by
    intro b hb
    obtain ⟨β, hβ, rfl⟩ := Subgroup.mem_map.1 hb
    exact ⟨β, Subgroup.mem_subgroupOf.1 hβ, rfl⟩
  have h𝔹 : ∀ b ∈ 𝔹, inn b ∧ b ^ p = 1 ∧ b * u = u * b := by
    intro b hb
    obtain ⟨β, hβ, rfl⟩ := h𝔹mem b hb
    refine ⟨hinn β hβ, ?_, ?_⟩
    · rw [← map_pow]
      have : β ^ p = 1 := Subtype.ext (by simpa using hBel.2 (β : Ω) β.2)
      rw [this, map_one]
    · rw [hu, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hBab _ β.2 x hxB)
  set Y₀ : Subgroup Ω := T' ⊓ Subgroup.centralizer ({x} : Set Ω) with hY₀
  set Y : Subgroup P := (Y₀.subgroupOf S).map σ with hY
  have hYfix : Y ≤ fixSubgroup u := by
    rintro _ ⟨s, hs, rfl⟩
    have hsC : (s : Ω) ∈ Subgroup.centralizer ({x} : Set Ω) :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs)).2
    have hαs : α s = s := (sd_mem_fix_iff hBN xB s).2 hsC
    show u (σ s) = σ s
    rw [hu, hρ, hσ, sd_rho_apply hBN θ xB s, hαs]
  have hY2 : IsPGroup 2 ↥Y :=
    (((hT'2.to_le (inf_le_left : Y₀ ≤ T')).comap_subtype (K := S))).map σ
  have hYinv : ∀ β : ↥B, (β : Ω) ∈ B₀ → ∀ y ∈ Y, ρ β y ∈ Y := by
    intro β hβ y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hy
    have hsT : (s : Ω) ∈ T' := (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs)).1
    have hsC : (s : Ω) ∈ Subgroup.centralizer ({x} : Set Ω) :=
      (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hs)).2
    rw [hρ, hσ, sd_rho_apply hBN θ β s]
    refine Subgroup.mem_map.2 ⟨CFSG.normalizerConjAutOfMem S B hBN β s, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, hY₀, Subgroup.mem_inf, sd_conj_coe]
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hBT' β.2) _).1 hsT, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hsC ⊢
    have hc1 : Commute x (β : Ω) := (hBab x hxB β β.2)
    have hc2 : Commute x (s : Ω) := hsC.symm
    exact ((hc1.mul_right hc2).mul_right hc1.inv_right).eq.symm
  have hYmap : ∀ b ∈ 𝔹, Y.map b.toMonoidHom = Y := by
    intro b hb
    obtain ⟨β, hβ, rfl⟩ := h𝔹mem b hb
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact hYinv β hβ y hy
    · intro y hy
      refine ⟨(ρ β)⁻¹ y, ?_, ?_⟩
      · have : (ρ β)⁻¹ = ρ β⁻¹ := (map_inv ρ β).symm
        rw [this]
        exact hYinv β⁻¹ (B₀.inv_mem hβ) y hy
      · simp
  have hcomm : autComm 𝔹 Y ≠ ⊥ := by
    intro hbot
    apply hS₁
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro β hβ
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    have htS : t ∈ S := hT'S (Subgroup.mem_inf.1 ht).1
    let β' : ↥B := ⟨β, hB₀B hβ⟩
    let ts : ↥S := ⟨t, htS⟩
    have hz : (ρ β') (σ ts) * (σ ts)⁻¹ ∈ autComm 𝔹 Y :=
      Subgroup.subset_closure ⟨ρ β', Subgroup.mem_map.2 ⟨β', Subgroup.mem_subgroupOf.2 hβ, rfl⟩,
        σ ts, Subgroup.mem_map.2 ⟨ts, Subgroup.mem_subgroupOf.2 ht, rfl⟩, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hz
    rw [hρ, hσ, sd_rho_apply hBN θ β' ts, ← map_inv, ← map_mul] at hz
    have hcen : (CFSG.normalizerConjAutOfMem S B hBN β' ts * ts⁻¹) ∈ Subgroup.center ↥S :=
      (sdσ_eq_one_iff θ _).1 hz
    have hcoe : ((CFSG.normalizerConjAutOfMem S B hBN β' ts * ts⁻¹ : ↥S) : Ω) = ⁅β, t⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, sd_conj_coe, commutatorElement_def]
    have hT'mem : ⁅β, t⁆ ∈ T' := by
      rw [commutatorElement_def]
      have h1 : β * t * β⁻¹ ∈ T' :=
        (Subgroup.mem_normalizer_iff.1 (hBT' (hB₀B hβ)) t).1 (Subgroup.mem_inf.1 ht).1
      exact T'.mul_mem h1 (T'.inv_mem (Subgroup.mem_inf.1 ht).1)
    obtain ⟨k, hk⟩ := hT'2 ⟨⁅β, t⁆, hT'mem⟩
    have hk' : ⁅β, t⁆ ^ (2 ^ k) = 1 := congrArg Subtype.val hk
    have hz1 := sd_center_two_trivial hp hp2 hSp hcen (k := k) (by
      apply Subtype.ext
      rw [Subgroup.coe_pow, hcoe]
      exact hk')
    have : ⁅β, t⁆ = 1 := by
      have := congrArg Subtype.val hz1
      rw [← hcoe]
      exact this
    rw [commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  obtain ⟨JP, hJPc, hJPp, hJPa, hJPi⟩ := hF u huinn hup hu1 𝔹 h𝔹 Y hYfix hY2 hYmap hcomm
  obtain ⟨J₀, hJ₀C, hJ₀map, hJ₀sub, hJ₀q, ⟨hJ₀e⟩, hJ₀cent⟩ :=
    sd_lift_component σ hσs hσker α u hαβ hJPc
  let ρS : ↥J₀ ≃* ↥(J₀.map S.subtype) := Subgroup.equivMapOfInjective J₀ S.subtype S.subtype_injective
  have hmapfix : (fixSubgroup α).map S.subtype = S ⊓ Subgroup.centralizer ({x} : Set Ω) := by
    ext y
    constructor
    · rintro ⟨s, hs, rfl⟩
      exact Subgroup.mem_inf.2 ⟨s.2, (sd_mem_fix_iff hBN xB s).1 hs⟩
    · intro hy
      obtain ⟨hyS, hyC⟩ := Subgroup.mem_inf.1 hy
      exact ⟨⟨y, hyS⟩, (sd_mem_fix_iff hBN xB ⟨y, hyS⟩).2 hyC, rfl⟩
  have hJX : J₀.map S.subtype ≤ S ⊓ Subgroup.centralizer ({x} : Set Ω) := by
    rw [← hmapfix]
    exact Subgroup.map_mono hJ₀C
  have hJsub : IsSubnormal (J₀.map S.subtype) (S ⊓ Subgroup.centralizer ({x} : Set Ω)) := by
    have := hJ₀sub.map S.subtype
    rwa [hmapfix] at this
  have hJq : CFSG.Open.IsQuasisimple ↥(J₀.map S.subtype) :=
    CFSG.Open.IsQuasisimple.of_mulEquiv ρS.symm hJ₀q
  have ε₁ : ↥(J₀.map S.subtype) ⧸ Subgroup.center ↥(J₀.map S.subtype) ≃*
      ↥J₀ ⧸ Subgroup.center ↥J₀ :=
    QuotientGroup.congr _ _ ρS.symm (Subgroup.map_center_eq ρS.symm)
  have ε := ε₁.trans hJ₀e
  refine ⟨J₀.map S.subtype, ⟨⟨hJX, hJsub, hJq⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [Nat.card_congr ε.toEquiv]
    exact hJPp
  ·
    intro hbot
    apply hJPa
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro z hz
    have hz' := sd_autComm_le (B := B) (B₀ := B₀) (T' := T') (x := x) hSn θ hz
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hz'
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    rw [← hJ₀map] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hbot
      (Subgroup.mem_subgroupOf.1 hs)
    have h2 : (j : Ω) * s = s * j :=
      Subgroup.mem_centralizer_iff.1 h1 (j : Ω) (Subgroup.mem_map_of_mem S.subtype hj)
    change σ j * σ s = σ s * σ j
    rw [← map_mul, ← map_mul]
    exact congrArg σ (Subtype.ext h2)
  ·
    intro s hs
    have hsS : s ∈ S := hT'S (sd_S₁_le_T' hB₀B hBT' hs)
    have hsC : s ∈ Subgroup.centralizer ({x} : Set Ω) := sd_S₁_le_C hBab hB₀B hxB₀ hs
    have hmem : σ ⟨s, hsS⟩ ∈ autComm 𝔹 Y :=
      sd_le_autComm hSn θ hB₀B hT'S ⟨⟨s, hsS⟩, Subgroup.mem_subgroupOf.2 hs, rfl⟩
    have hmem2 := hJPi hmem
    obtain ⟨b, hb, c, hc, hbc⟩ := sd_mem_sup_of_commute (H := JP)
      (K := fixSubgroup u ⊓ Subgroup.centralizer (JP : Set P))
      (fun a ha c hc => Subgroup.mem_centralizer_iff.1 hc.2 a ha) hmem2
    rw [← hJ₀map] at hb
    obtain ⟨j, hj, rfl⟩ := hb
    set d : ↥S := j⁻¹ * ⟨s, hsS⟩ with hd
    have hσd : σ d = c := by
      rw [hd, map_mul, map_inv, hbc]
      exact inv_mul_cancel_left _ _
    have hdcent : d ∈ Subgroup.centralizer (J₀ : Set ↥S) :=
      hJ₀cent d (by rw [hσd]; exact hc.2)
    have hjJ : (j : Ω) ∈ J₀.map S.subtype := Subgroup.mem_map_of_mem S.subtype hj
    have hdD : (d : Ω) ∈ S ⊓ Subgroup.centralizer ({x} : Set Ω) ⊓
        Subgroup.centralizer ((J₀.map S.subtype : Subgroup Ω) : Set Ω) := by
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_inf.2 ⟨d.2, ?_⟩, ?_⟩
      · have hjC := (hJX hjJ).2
        have : (d : Ω) = (j : Ω)⁻¹ * s := rfl
        rw [this]
        exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hjC) hsC
      · rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨j', hj', rfl⟩
        exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.1 hdcent j' hj')
    have hs_eq : s = (j : Ω) * (d : Ω) := by
      simp [hd]
    rw [hs_eq]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hjJ) (Subgroup.mem_sup_right hdD)
  ·
    have hTs : IsSimpleGroup P := by
      haveI : IsSimpleGroup (↥S ⧸ Subgroup.center ↥S) := hSq.2
      exact θ.symm.isSimpleGroup
    have hTnc : ∃ a b : P, a * b ≠ b * a := by
      obtain ⟨a, b, hab⟩ := (native_of_open_dx hSq).2.2
      exact ⟨θ a, θ b, fun h => hab (θ.injective (by rwa [map_mul, map_mul]))⟩
    have hcomp : IsComponentOf JP (CFSG.LocalAnalysis.GLTheoremA.I142.centFix
        (Subgroup.zpowers u)) := by
      rw [sd_centFix_zpowers_eq]
      exact hJPc
    exact t263_isChevSimple_congr ε.symm
      (hChev P hTs hTnc (t263_isChevSimple_congr θ hSc) p hp hp2 u hup hu1 JP hcomp)

end CFSG.LocalAnalysis.GLTheoremA.T263.SD

end
