module

public import CFSG.ClassicalInvolution.Asc77.AscC5O10A
public import CFSG.ClassicalInvolution.Asc77.AscC5O10L
public import CFSG.ClassicalInvolution.Asc77.AscC5OM8GStmt

public section

namespace CFSG.ClassicalInvolution.Asc77.C5O

open CFSG.Open (classicalInvolutionOddCore)
open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Disconnected
  CFSG.ClassicalInvolution.Asc77.ExactLayer CFSG.ClassicalInvolution.Balance
  CFSG.ClassicalInvolution.Balance.Bootstrap

variable {G : Type} [Group G] [Finite G]

@[expose] def twinM (a : G) (K K' : Subgroup G) : Subgroup G := exactCore a K ⊔ exactCore a K'

@[expose] noncomputable def twinπ (Ω : Set (Subgroup G)) (c : G) {M : Subgroup G}
    (h : M ≤ exactLayer Ω c) :
    ↥M →* ↥(exactLayer Ω c) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω c) :=
  (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω c))).comp (Subgroup.inclusion h)

theorem twinπ_apply (Ω : Set (Subgroup G)) (c : G) {M : Subgroup G} (h : M ≤ exactLayer Ω c)
    (m : ↥M) : twinπ Ω c h m = QuotientGroup.mk ⟨(m : G), h m.2⟩ := rfl

theorem map_twinπ (Ω : Set (Subgroup G)) (c : G) {M B : Subgroup G} (h : M ≤ exactLayer Ω c)
    (hB : B ≤ M) : (B.subgroupOf M).map (twinπ Ω c h) =
      (B.subgroupOf (exactLayer Ω c)).map
        (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω c))) := by
  ext e
  constructor
  · rintro ⟨m, hm, rfl⟩
    exact ⟨⟨m, h m.2⟩, hm, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨⟨y, hB hy⟩, hy, rfl⟩

theorem odd_card_ker_twinπ (Ω : Set (Subgroup G)) (c : G) {M : Subgroup G}
    (h : M ≤ exactLayer Ω c) : Odd (Nat.card (twinπ Ω c h).ker) := by
  have h1 : Nat.card ((twinπ Ω c h).ker.map M.subtype) = Nat.card (twinπ Ω c h).ker :=
    Subgroup.card_map_of_injective M.subtype_injective
  have h2 : (twinπ Ω c h).ker.map M.subtype ≤ oddCoreIn (exactLayer Ω c) := by
    rintro _ ⟨m, hm, rfl⟩
    exact (mk_eq_one_iff (exactLayer Ω c) ⟨m, h m.2⟩).mp hm
  rw [← h1]
  exact Odd.of_dvd_nat (odd_card_oddCoreIn _) (Subgroup.card_dvd_of_le h2)

omit [Finite G] in
theorem layerAut_symm_apply (Y : Subgroup G) {x : G} (hx : conjSub x Y = Y)
    (hxi : conjSub x⁻¹ Y = Y) (e : ↥Y ⧸ classicalInvolutionOddCore ↥Y) :
    (C25Y.layerAut Y hx).symm e = C25Y.layerAut Y hxi e := by
  induction e using QuotientGroup.induction_on with
  | H w =>
    rw [MulEquiv.symm_apply_eq, C25Y.layerAut_mk, C25Y.layerAut_mk]
    congr 1
    apply Subtype.ext
    simp only [C25Y.coe_conjOnSub]
    group

omit [Finite G] in
theorem layerAut_comm_apply (Y : Subgroup G) {x y : G} (hx : conjSub x Y = Y)
    (hy : conjSub y Y = Y) (hc : conjSub (x * y * x⁻¹ * y⁻¹) Y = Y)
    (e : ↥Y ⧸ classicalInvolutionOddCore ↥Y) :
    C25Y.layerAut Y hc e = C25Y.layerAut Y hx (C25Y.layerAut Y hy
      ((C25Y.layerAut Y hx).symm ((C25Y.layerAut Y hy).symm e))) := by
  have hxi : conjSub x⁻¹ Y = Y := by rw [← hx, ← conjSub_mul, inv_mul_cancel, conjSub_one, hx]
  have hyi : conjSub y⁻¹ Y = Y := by rw [← hy, ← conjSub_mul, inv_mul_cancel, conjSub_one, hy]
  have h1 : conjSub (x * y) Y = Y := by rw [conjSub_mul, hy, hx]
  have h2 : conjSub (x * y * x⁻¹) Y = Y := by rw [conjSub_mul, hxi, h1]
  rw [layerAut_symm_apply Y hy hyi, layerAut_symm_apply Y hx hxi,
    layerAut_mul_apply Y h2 hyi hc, layerAut_mul_apply Y h1 hxi h2,
    layerAut_mul_apply Y hx hy h1]

theorem mul_inv_mem_trivialOnQuot (Y : Subgroup G) {c w : G} (hw : w ∈ Y)
    (hc : conjSub c Y = Y)
    (h : ∀ e, C25Y.layerAut Y hc e =
      QuotientGroup.mk ⟨w, hw⟩ * e * (QuotientGroup.mk ⟨w, hw⟩)⁻¹) :
    c * w⁻¹ ∈ trivialOnQuot Y := by
  have hwi : conjSub w⁻¹ Y = Y := conjSub_eq_self_of_mem (inv_mem hw)
  have hcw : conjSub (c * w⁻¹) Y = Y := by rw [conjSub_mul, hwi, hc]
  rw [← layerAut_eq_id_iff Y hcw]
  intro e
  rw [layerAut_mul_apply _ hc hwi hcw, h, layerAut_of_mem _ (inv_mem hw)]
  have e1 : (QuotientGroup.mk ⟨w⁻¹, inv_mem hw⟩ : ↥Y ⧸ classicalInvolutionOddCore ↥Y) =
      (QuotientGroup.mk ⟨w, hw⟩)⁻¹ := by
    rw [← QuotientGroup.mk_inv]; rfl
  rw [e1]
  group

variable {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K K' W : Subgroup G} {S : Sylow 2 G} {R R' : Subgroup G} {z t u₁ u₂ a : G}

namespace Swaps

variable {τ σ : G}

theorem twinShare [IsSimpleGroup G] (hM : ModelFacts p f)
    (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ)
    (hzY : z ∈ exactLayer Ω a) (hu₁Y : u₁ ∈ exactLayer Ω a) (hu₂Y : u₂ ∈ exactLayer Ω a)
    (hzY' : z ∈ exactLayer Ω (a * z)) (hu₁Y' : u₁ ∈ exactLayer Ω (a * z))
    (hu₂Y' : u₂ ∈ exactLayer Ω (a * z))
    (hMa : twinM a K K' ≤ exactLayer Ω a) (hMaz : twinM a K K' ≤ exactLayer Ω (a * z)) :
    TwinShare p f (oddQuotientFamily (exactPair Ω a)) (T7H.exactImg Ω a K)
      (T7H.exactImg Ω a K') (T7H.toBar Ω a z hzY) (T7H.toBar Ω a u₁ hu₁Y)
      (T7H.toBar Ω a u₂ hu₂Y) (oddQuotientFamily (exactPair Ω (a * z)))
      (T7H.exactImg Ω (a * z) K) (T7H.exactImg Ω (a * z) K') (T7H.toBar Ω (a * z) z hzY')
      (T7H.toBar Ω (a * z) u₁ hu₁Y') (T7H.toBar Ω (a * z) u₂ hu₂Y')
      (twinπ Ω a hMa) (twinπ Ω (a * z) hMaz)
      ((exactCore a K).subgroupOf (twinM a K K'))
      ((exactCore a K').subgroupOf (twinM a K K')) := by
  classical
  have C := D.ctx
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hzY₀, hu₁Y₀, hu₂Y₀, hK₂, hK₂', hD⟩ := C.om5
  obtain ⟨hzY₁, hu₁Y₁, hu₂Y₁, hK₃, hK₃', hD'⟩ := C.swap.om5
  have hcK := exactCore_le_exactLayer hK₂
  have hcK' := exactCore_le_exactLayer hK₂'
  have hcKz := C.exactCore_az ▸ exactCore_le_exactLayer hK₃
  have hcKz' := C.exactCore_az' ▸ exactCore_le_exactLayer hK₃'
  have hL : exactCore a K ≤ twinM a K K' := le_sup_left
  have hL' : exactCore a K' ≤ twinM a K K' := le_sup_right
  have hrange : ∀ (c : G) (hc : twinM a K K' ≤ exactLayer Ω c),
      exactCore a K ≤ exactLayer Ω c → exactCore a K' ≤ exactLayer Ω c →
      (twinπ Ω c hc).range =
        ((exactCore a K).subgroupOf (exactLayer Ω c)).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω c))) ⊔
        ((exactCore a K').subgroupOf (exactLayer Ω c)).map
          (QuotientGroup.mk' (classicalInvolutionOddCore ↥(exactLayer Ω c))) := by
    intro c hc h1 h2
    rw [MonoidHom.range_eq_map, ← Subgroup.subgroupOf_self, map_twinπ Ω c hc le_rfl, twinM,
      Subgroup.subgroupOf_sup h1 h2, Subgroup.map_sup]
  have hτ2 : τ * τ = 1 := by
    obtain ⟨cτ, hcτ⟩ := D.τG
    rw [← hcτ]
    calc cτ * z * cτ⁻¹ * (cτ * z * cτ⁻¹) = cτ * (z * z) * cτ⁻¹ := by group
      _ = 1 := by rw [C.hz2]; group
  have hτaC : τ * a * τ⁻¹ = a := by rw [D.τa]; group
  have hτK' : conjSub τ K' = K := by rw [← D.τK, ← conjSub_mul, hτ2, conjSub_one]
  have hcτ1 : conjSub τ (exactCore a K) = exactCore a K' := by
    rw [← exactCore_conjSub, hτaC, D.τK]
  have hcτ2 : conjSub τ (exactCore a K') = exactCore a K := by
    rw [← exactCore_conjSub, hτaC, hτK']
  have hτM : ∀ m ∈ twinM a K K', τ * m * τ⁻¹ ∈ twinM a K K' := by
    intro m hm
    have h1 : τ * m * τ⁻¹ ∈ conjSub τ (twinM a K K') := ⟨m, hm, rfl⟩
    have h2 : conjSub τ (twinM a K K') = twinM a K K' := by
      unfold twinM
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, hcτ1, hcτ2, sup_comm]
    rwa [h2] at h1
  have hτXa : conjSub τ (exactLayer Ω a) = exactLayer Ω a :=
    conjSub_exactLayer hΩ.conjInvariant D.τC
  have hτXaz : conjSub τ (exactLayer Ω (a * z)) = exactLayer Ω (a * z) :=
    conjSub_eq_self_of_mem D.τX
  obtain ⟨D₀, hD1, i₀, hDi⟩ := hD.lie
  have hD4 : ∀ i, D₀.tag i ≠ .G2 ∧ D₀.tag i ≠ .trialityD4 := by
    intro i
    have hi : i = i₀ := Fin.ext (by have h1 := i.2; have h2 := i₀.2; omega)
    subst hi
    simp only [IsOrthTag] at hDi
    rcases hDi with ⟨-, ht, -⟩ | ⟨h6, -⟩ | ⟨h6, -⟩ | ⟨h7, -⟩ | ⟨h8, -⟩ | ⟨h8, -⟩
    · rw [ht]; exact ⟨by decide, by decide⟩
    all_goals omega
  obtain ⟨cτ, hcτ⟩ := D.τG
  refine ⟨hD, hD', ?_, ?_, odd_card_ker_twinπ Ω a hMa, odd_card_ker_twinπ Ω (a * z) hMaz,
    ⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · rw [hrange a hMa hcK hcK']; rfl
  · rw [hrange (a * z) hMaz hcKz hcKz']
    unfold T7H.exactImg
    rw [C.exactCore_az, C.exactCore_az']
  · rw [map_twinπ Ω a hMa hL]; rfl
  · rw [map_twinπ Ω a hMa hL']; rfl
  · rw [map_twinπ Ω (a * z) hMaz hL]
    unfold T7H.exactImg
    rw [C.exactCore_az]
  · rw [map_twinπ Ω (a * z) hMaz hL']
    unfold T7H.exactImg
    rw [C.exactCore_az']
  · refine ⟨fun m => ⟨τ * m * τ⁻¹, hτM m m.2⟩, C25Y.layerAut _ hτXa, C25Y.layerAut _ hτXaz,
      fun m hm => ?_, fun m hm => ?_, fun m => rfl, fun m => rfl,
      ⟨QuotientGroup.mk ⟨τ, D.τX⟩, fun x => layerAut_of_mem _ D.τX hτXaz x⟩,
      C25Y.layerAut_involutive _ hτXa hτ2, ?_, C.not_hasBigFix hM hτ2 hτXa hcτ⟩
    · have h1 : τ * (m : G) * τ⁻¹ ∈ conjSub τ (exactCore a K) := ⟨m, hm, rfl⟩
      rw [hcτ1] at h1
      exact h1
    · have h1 : τ * (m : G) * τ⁻¹ ∈ conjSub τ (exactCore a K') := ⟨m, hm, rfl⟩
      rw [hcτ2] at h1
      exact h1
    · intro J hJ x hxJ hx4 hx2 hfix
      have hwC : cτ * z * cτ⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
        rw [hcτ]; exact D.τC
      subst hcτ
      obtain ⟨h, hhC, hh⟩ := C25Y.c25_8_one C.hyp C.ha2 hzY hK₂ D₀ hD1 hD4 hwC hJ hxJ hx4 hx2
        hfix
      exact D.τn h (Subgroup.mem_centralizer_singleton_iff.mp hhC) hh

theorem comm_mem_hInf_fix [IsSimpleGroup G] (hM : ModelFacts p f) (hM8 : M8GFacts p f)
    (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ) {x y : G}
    (hxa : x * a = a * x) (hxz : x * z = z * x) (hxK : conjSub x K = K)
    (hya : y * a = a * y) (hyz : y * z = z * y) (hyK : conjSub y K = K) :
    x * y * x⁻¹ * y⁻¹ ∈ hSub D.ctx.hyp.std.setting.stand.hyp.conjInvariant a τ D.τC ⊓
      hSub D.ctx.hyp.std.setting.stand.hyp.conjInvariant (a * z) σ D.σC := by
  classical
  have C := D.ctx
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', -⟩ := C.om5
  obtain ⟨hzY', hu₁Y', hu₂Y', hK₃, hK₃', -⟩ := C.swap.om5
  have hMa : twinM a K K' ≤ exactLayer Ω a :=
    sup_le (exactCore_le_exactLayer hK₂) (exactCore_le_exactLayer hK₂')
  have hMaz : twinM a K K' ≤ exactLayer Ω (a * z) :=
    sup_le (C.exactCore_az ▸ exactCore_le_exactLayer hK₃)
      (C.exactCore_az' ▸ exactCore_le_exactLayer hK₃')
  have TS := D.twinShare hM hzY hu₁Y hu₂Y hzY' hu₁Y' hu₂Y' hMa hMaz
  have hcA : ∀ v : G, v * a = a * v → v * z = z * v →
      v ∈ Subgroup.centralizer ({a} : Set G) ∧ v ∈ Subgroup.centralizer ({a * z} : Set G) := by
    intro v hva hvz
    refine ⟨Subgroup.mem_centralizer_singleton_iff.mpr hva,
      Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    calc v * (a * z) = (v * a) * z := by group
      _ = a * (v * z) := by rw [hva]; group
      _ = a * z * v := by rw [hvz]; group
  obtain ⟨hxCa, hxCaz⟩ := hcA x hxa hxz
  obtain ⟨hyCa, hyCaz⟩ := hcA y hya hyz
  have hK'of : ∀ v : G, v * z = z * v → conjSub v K = K → conjSub v K' = K' := by
    intro v hvz hvK
    have hvz' : v * z * v⁻¹ = z := by rw [hvz]; group
    rcases C25Y.conjSub_pair_of_central hs hvz' with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (hvK.symm.trans h1) hs.hne.symm
  have hxK' := hK'of x hxz hxK
  have hyK' := hK'of y hyz hyK
  have hMv : ∀ v : G, v * a = a * v → conjSub v K = K → conjSub v K' = K' →
      ∀ m ∈ twinM a K K', v * m * v⁻¹ ∈ twinM a K K' := by
    intro v hva hvK hvK' m hm
    have hva' : v * a * v⁻¹ = a := by rw [hva]; group
    have h1 : conjSub v (exactCore a K) = exactCore a K := by
      rw [← exactCore_conjSub, hva', hvK]
    have h2 : conjSub v (exactCore a K') = exactCore a K' := by
      rw [← exactCore_conjSub, hva', hvK']
    have h3 : conjSub v (twinM a K K') = twinM a K K' := by
      unfold twinM
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, h1, h2]
    have : v * m * v⁻¹ ∈ conjSub v (twinM a K K') := ⟨m, hm, rfl⟩
    rwa [h3] at this
  set hX := hΩ.conjInvariant with hXdef
  have hxXa : conjSub x (exactLayer Ω a) = exactLayer Ω a := conjSub_exactLayer hX hxCa
  have hxXaz : conjSub x (exactLayer Ω (a * z)) = exactLayer Ω (a * z) :=
    conjSub_exactLayer hX hxCaz
  have hyXa : conjSub y (exactLayer Ω a) = exactLayer Ω a := conjSub_exactLayer hX hyCa
  have hyXaz : conjSub y (exactLayer Ω (a * z)) = exactLayer Ω (a * z) :=
    conjSub_exactLayer hX hyCaz
  obtain ⟨w, hw1, hw2⟩ := hM8.comm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TS
    (C25Y.layerAut _ hxXa) (C25Y.layerAut _ hyXa) (C25Y.layerAut _ hxXaz)
    (C25Y.layerAut _ hyXaz)
    (by rw [map_exactImg_layerAut hX hxCa, hxK]) (by rw [map_exactImg_layerAut hX hxCa, hxK'])
    (by rw [map_exactImg_layerAut hX hxCaz, hxK]) (by rw [map_exactImg_layerAut hX hxCaz, hxK'])
    (by rw [map_exactImg_layerAut hX hyCa, hyK]) (by rw [map_exactImg_layerAut hX hyCa, hyK'])
    (by rw [map_exactImg_layerAut hX hyCaz, hyK]) (by rw [map_exactImg_layerAut hX hyCaz, hyK'])
    (fun m => ⟨⟨x * m * x⁻¹, hMv x hxa hxK hxK' m m.2⟩, rfl, rfl⟩)
    (fun m => ⟨⟨y * m * y⁻¹, hMv y hya hyK hyK' m m.2⟩, rfl, rfl⟩)
  have hwa : (w : G) ∈ exactLayer Ω a := hMa w.2
  have hwaz : (w : G) ∈ exactLayer Ω (a * z) := hMaz w.2
  have hcCa : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
    mul_mem (mul_mem (mul_mem hxCa hyCa) (inv_mem hxCa)) (inv_mem hyCa)
  have hcCaz : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a * z} : Set G) :=
    mul_mem (mul_mem (mul_mem hxCaz hyCaz) (inv_mem hxCaz)) (inv_mem hyCaz)
  have htriv : ∀ (b : G) (hcb : x * y * x⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({b} : Set G))
      (hwb : (w : G) ∈ exactLayer Ω b) (hMb : twinM a K K' ≤ exactLayer Ω b)
      (hxb : conjSub x (exactLayer Ω b) = exactLayer Ω b)
      (hyb : conjSub y (exactLayer Ω b) = exactLayer Ω b),
      (∀ e, C25Y.layerAut _ hxb (C25Y.layerAut _ hyb ((C25Y.layerAut _ hxb).symm
        ((C25Y.layerAut _ hyb).symm e))) = twinπ Ω b hMb w * e * (twinπ Ω b hMb w)⁻¹) →
      x * y * x⁻¹ * y⁻¹ * (w : G)⁻¹ ∈ trivialOnQuot (exactLayer Ω b) := by
    intro b hcb hwb hMb hxb hyb hw
    have hcX : conjSub (x * y * x⁻¹ * y⁻¹) (exactLayer Ω b) = exactLayer Ω b :=
      conjSub_exactLayer hX hcb
    have hwi : conjSub (w : G)⁻¹ (exactLayer Ω b) = exactLayer Ω b :=
      conjSub_eq_self_of_mem (inv_mem hwb)
    have hcw : conjSub (x * y * x⁻¹ * y⁻¹ * (w : G)⁻¹) (exactLayer Ω b) = exactLayer Ω b := by
      rw [conjSub_mul, hwi, hcX]
    rw [← layerAut_eq_id_iff (exactLayer Ω b) hcw]
    intro e
    rw [layerAut_mul_apply _ hcX hwi hcw, layerAut_comm_apply _ hxb hyb hcX, hw,
      layerAut_of_mem _ (inv_mem hwb), twinπ_apply]
    have e1 : (QuotientGroup.mk ⟨(w : G)⁻¹, inv_mem hwb⟩ :
        ↥(exactLayer Ω b) ⧸ classicalInvolutionOddCore ↥(exactLayer Ω b)) =
        (QuotientGroup.mk ⟨(w : G), hwb⟩)⁻¹ := by
      rw [← QuotientGroup.mk_inv]; rfl
    rw [e1]
    group
  exact D.mem_hInf_of_triv hM hcCa hcCaz hwa hwaz
    (htriv a hcCa hwa hMa hxXa hyXa hw1) (htriv (a * z) hcCaz hwaz hMaz hxXaz hyXaz hw2)

theorem comm_mem_hInf_swap [IsSimpleGroup G] (hM : ModelFacts p f) (hM8 : M8GFacts p f)
    (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ) {g y : G}
    (hga : g * a * g⁻¹ = a * z) (hgz : g * z = z * g) (hgK : conjSub g K = K)
    (hya : y * a = a * y) (hyz : y * z = z * y) (hyK : conjSub y K = K) :
    g * y * g⁻¹ * y⁻¹ ∈ hSub D.ctx.hyp.std.setting.stand.hyp.conjInvariant a τ D.τC ⊓
      hSub D.ctx.hyp.std.setting.stand.hyp.conjInvariant (a * z) σ D.σC := by
  classical
  have C := D.ctx
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hΩ : HypOmegaMod p f Ω := hs.stand.hyp
  obtain ⟨hzY, hu₁Y, hu₂Y, hK₂, hK₂', -⟩ := C.om5
  obtain ⟨hzY', hu₁Y', hu₂Y', hK₃, hK₃', -⟩ := C.swap.om5
  have hMa : twinM a K K' ≤ exactLayer Ω a :=
    sup_le (exactCore_le_exactLayer hK₂) (exactCore_le_exactLayer hK₂')
  have hMaz : twinM a K K' ≤ exactLayer Ω (a * z) :=
    sup_le (C.exactCore_az ▸ exactCore_le_exactLayer hK₃)
      (C.exactCore_az' ▸ exactCore_le_exactLayer hK₃')
  have TS := D.twinShare hM hzY hu₁Y hu₂Y hzY' hu₁Y' hu₂Y' hMa hMaz
  set hX := hΩ.conjInvariant with hXdef
  have hgz' : g * z * g⁻¹ = z := by rw [hgz]; group
  have hga' : g * (a * z) * g⁻¹ = a := by
    calc g * (a * z) * g⁻¹ = (g * a * g⁻¹) * (g * z * g⁻¹) := by group
      _ = a := by rw [hga, hgz', C.mul_z_mul_z]
  have hK'of : ∀ v : G, v * z * v⁻¹ = z → conjSub v K = K → conjSub v K' = K' := by
    intro v hvz hvK
    rcases C25Y.conjSub_pair_of_central hs hvz with ⟨-, h2⟩ | ⟨h1, -⟩
    · exact h2
    · exact absurd (hvK.symm.trans h1) hs.hne.symm
  have hgK' := hK'of g hgz' hgK
  have hyz' : y * z * y⁻¹ = z := by rw [hyz]; group
  have hyK' := hK'of y hyz' hyK
  have hyCa : y ∈ Subgroup.centralizer ({a} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hya
  have hyCaz : y ∈ Subgroup.centralizer ({a * z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    calc y * (a * z) = (y * a) * z := by group
      _ = a * (y * z) := by rw [hya]; group
      _ = a * z * y := by rw [hyz]; group
  have hyXa : conjSub y (exactLayer Ω a) = exactLayer Ω a := conjSub_exactLayer hX hyCa
  have hyXaz : conjSub y (exactLayer Ω (a * z)) = exactLayer Ω (a * z) :=
    conjSub_exactLayer hX hyCaz
  have hMv : ∀ (v : G) (b : G), v * a * v⁻¹ = b → exactCore b K = exactCore a K →
      exactCore b K' = exactCore a K' → conjSub v K = K → conjSub v K' = K' →
      ∀ m ∈ twinM a K K', v * m * v⁻¹ ∈ twinM a K K' := by
    intro v b hvb hb hb' hvK hvK' m hm
    have h1 : conjSub v (exactCore a K) = exactCore a K := by
      rw [← exactCore_conjSub, hvb, hvK, hb]
    have h2 : conjSub v (exactCore a K') = exactCore a K' := by
      rw [← exactCore_conjSub, hvb, hvK', hb']
    have h3 : conjSub v (twinM a K K') = twinM a K K' := by
      unfold twinM
      rw [conjSub, Subgroup.map_sup, ← conjSub, ← conjSub, h1, h2]
    have : v * m * v⁻¹ ∈ conjSub v (twinM a K K') := ⟨m, hm, rfl⟩
    rwa [h3] at this
  have hya' : y * a * y⁻¹ = a := by rw [hya]; group
  obtain ⟨w, hw1, hw2⟩ := hM8.commSwap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ TS
    (layerIso hX hga) (layerIso hX hga') (C25Y.layerAut _ hyXa) (C25Y.layerAut _ hyXaz)
    (by rw [map_exactImg_layerIso, hgK]) (by rw [map_exactImg_layerIso, hgK'])
    (by rw [map_exactImg_layerIso, hgK]) (by rw [map_exactImg_layerIso, hgK'])
    (by rw [map_exactImg_layerAut hX hyCa, hyK]) (by rw [map_exactImg_layerAut hX hyCa, hyK'])
    (by rw [map_exactImg_layerAut hX hyCaz, hyK]) (by rw [map_exactImg_layerAut hX hyCaz, hyK'])
    (fun m => ⟨⟨g * m * g⁻¹, hMv g (a * z) hga C.exactCore_az C.exactCore_az' hgK hgK' m m.2⟩,
      rfl, rfl⟩)
    (fun m => ⟨⟨y * m * y⁻¹, hMv y a hya' rfl rfl hyK hyK' m m.2⟩, rfl, rfl⟩)
  have hwa : (w : G) ∈ exactLayer Ω a := hMa w.2
  have hwaz : (w : G) ∈ exactLayer Ω (a * z) := hMaz w.2
  have hgyCaz : g * y * g⁻¹ ∈ Subgroup.centralizer ({a} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h := Subgroup.mem_centralizer_singleton_iff.mp hyCaz
    calc g * y * g⁻¹ * a = g * (y * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = g * (y * (a * z)) * g⁻¹ := by
          rw [show g⁻¹ * a * g = a * z by
            calc g⁻¹ * a * g = g⁻¹ * (g * (a * z) * g⁻¹) * g := by rw [hga']
              _ = a * z := by group]
      _ = g * ((a * z) * y) * g⁻¹ := by rw [h]
      _ = (g * (a * z) * g⁻¹) * (g * y * g⁻¹) := by group
      _ = a * (g * y * g⁻¹) := by rw [hga']
  have hgyCa : g * y * g⁻¹ ∈ Subgroup.centralizer ({a * z} : Set G) := by
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have h := Subgroup.mem_centralizer_singleton_iff.mp hyCa
    calc g * y * g⁻¹ * (a * z) = g * (y * (g⁻¹ * (a * z) * g)) * g⁻¹ := by group
      _ = g * (y * a) * g⁻¹ := by
          rw [show g⁻¹ * (a * z) * g = a by
            calc g⁻¹ * (a * z) * g = g⁻¹ * (g * a * g⁻¹) * g := by rw [hga]
              _ = a := by group]
      _ = g * (a * y) * g⁻¹ := by rw [h]
      _ = (g * a * g⁻¹) * (g * y * g⁻¹) := by group
      _ = a * z * (g * y * g⁻¹) := by rw [hga]
  have hcCa : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a} : Set G) :=
    mul_mem hgyCaz (inv_mem hyCa)
  have hcCaz : g * y * g⁻¹ * y⁻¹ ∈ Subgroup.centralizer ({a * z} : Set G) :=
    mul_mem hgyCa (inv_mem hyCaz)
  have hyia : conjSub y⁻¹ (exactLayer Ω a) = exactLayer Ω a :=
    conjSub_exactLayer hX (inv_mem hyCa)
  have hyiaz : conjSub y⁻¹ (exactLayer Ω (a * z)) = exactLayer Ω (a * z) :=
    conjSub_exactLayer hX (inv_mem hyCaz)
  have hgyXa : conjSub (g * y * g⁻¹) (exactLayer Ω a) = exactLayer Ω a :=
    conjSub_exactLayer hX hgyCaz
  have hgyXaz : conjSub (g * y * g⁻¹) (exactLayer Ω (a * z)) = exactLayer Ω (a * z) :=
    conjSub_exactLayer hX hgyCa
  refine D.mem_hInf_of_triv hM hcCa hcCaz hwa hwaz
    (mul_inv_mem_trivialOnQuot _ hwa (conjSub_exactLayer hX hcCa) fun e => ?_)
    (mul_inv_mem_trivialOnQuot _ hwaz (conjSub_exactLayer hX hcCaz) fun e => ?_)
  · rw [layerAut_mul_apply _ hgyXa hyia, ← layerAut_symm_apply _ hyXa hyia,
      layerAut_conj hX hga' hyXaz hgyXa, hw1]
    rfl
  · rw [layerAut_mul_apply _ hgyXaz hyiaz, ← layerAut_symm_apply _ hyXaz hyiaz,
      layerAut_conj hX hga hyXa hgyXaz, hw2]
    rfl

theorem comm_mem_hBig [IsSimpleGroup G] (hM : ModelFacts p f) (hM8 : M8GFacts p f)
    (D : Swaps p f Ω K K' W S R R' z t u₁ u₂ a τ σ) (hτS : τ ∈ (S : Subgroup G)) :
    ∀ x ∈ (S : Subgroup G), ∀ y ∈ (S : Subgroup G), x * y * x⁻¹ * y⁻¹ ∈
      hBig D.ctx.hyp.std.setting.stand.hyp.conjInvariant z a τ σ D.τC D.σC := by
  classical
  have C := D.ctx
  have hs : Hyp23Setting p f Ω K K' z := C.hyp.std.setting
  have hΩ := D.ctx.hyp.std.setting.stand.hyp.conjInvariant
  obtain ⟨hzY', -, -, -, -, -⟩ := C.swap.om5
  have hτH₀ : τ ∈ hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC :=
    ⟨mem_hSub_self hΩ D.τC, le_hSub_layer hΩ D.σC D.τX⟩
  have hH₀ : hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC ≤ hBig hΩ z a τ σ D.τC D.σC :=
    le_mulSub_left _
  have hSz : ∀ v ∈ (S : Subgroup G), v * z * v⁻¹ = z := by
    intro v hv; rw [C.hyp.hzS v hv]; group
  set N₀ := (S : Subgroup G) ⊓ Subgroup.normalizer (K : Set G) with hN₀
  have hNK : ∀ v ∈ N₀, conjSub v K = K := fun v hv => conjSub_eq_of_mem_normalizer hv.2
  have hfix : ∀ v ∈ N₀, v * a * v⁻¹ = a → v * a = a * v := by
    intro v _ h
    calc v * a = (v * a * v⁻¹) * v := by group
      _ = a * v := by rw [h]
  have hcomm : ∀ x ∈ N₀, ∀ y ∈ N₀, x * a * x⁻¹ = a ∨ y * a * y⁻¹ = a →
      x * y * x⁻¹ * y⁻¹ ∈ hSub hΩ a τ D.τC ⊓ hSub hΩ (a * z) σ D.σC := by
    intro x hx y hy hxy
    rcases C.hconj x hx.1 with hxa | hxa <;> rcases C.hconj y hy.1 with hya | hya
    · exact D.comm_mem_hInf_fix hM hM8 (hfix x hx hxa) (C.hyp.hzS x hx.1) (hNK x hx)
        (hfix y hy hya) (C.hyp.hzS y hy.1) (hNK y hy)
    ·
      have h := D.comm_mem_hInf_swap hM hM8 hya (C.hyp.hzS y hy.1) (hNK y hy)
        (hfix x hx hxa) (C.hyp.hzS x hx.1) (hNK x hx)
      have e : x * y * x⁻¹ * y⁻¹ = (y * x * y⁻¹ * x⁻¹)⁻¹ := by group
      rw [e]; exact inv_mem h
    · exact D.comm_mem_hInf_swap hM hM8 hxa (C.hyp.hzS x hx.1) (hNK x hx)
        (hfix y hy hya) (C.hyp.hzS y hy.1) (hNK y hy)
    · rcases hxy with h | h
      · rw [h] at hxa; exact absurd (mul_left_cancel (a := a) (hxa.symm.trans (mul_one a).symm))
          C.hz1
      · rw [h] at hya; exact absurd (mul_left_cancel (a := a) (hya.symm.trans (mul_one a).symm))
          C.hz1
  have hcommN : ∀ x ∈ N₀, ∀ y ∈ N₀, x * y * x⁻¹ * y⁻¹ ∈ hBig hΩ z a τ σ D.τC D.σC := by
    intro x hx y hy
    by_cases hxa : x * a * x⁻¹ = a
    · exact hH₀ (hcomm x hx y hy (Or.inl hxa))
    by_cases hya : y * a * y⁻¹ = a
    · exact hH₀ (hcomm x hx y hy (Or.inr hya))
    have hxa' : x * a * x⁻¹ = a * z := (C.hconj x hx.1).resolve_left hxa
    have hya' : y * a * y⁻¹ = a * z := (C.hconj y hy.1).resolve_left hya
    have hyx : y * x⁻¹ ∈ N₀ := mul_mem hy (inv_mem hx)
    have hyxa : (y * x⁻¹) * a * (y * x⁻¹)⁻¹ = a := by
      have h1 : x⁻¹ * a * x = a * z := by
        have hz' : x⁻¹ * z * x = z := by
          have := hSz x⁻¹ (inv_mem hx.1)
          rwa [inv_inv] at this
        calc x⁻¹ * a * x = x⁻¹ * (x * a * x⁻¹ * z⁻¹) * x := by rw [hxa']; group
          _ = a * (x⁻¹ * z * x)⁻¹ := by group
          _ = a * z := by rw [hz', inv_eq_of_mul_eq_one_right C.hz2]
      calc (y * x⁻¹) * a * (y * x⁻¹)⁻¹ = y * (x⁻¹ * a * x) * y⁻¹ := by group
        _ = y * (a * z) * y⁻¹ := by rw [h1]
        _ = (y * a * y⁻¹) * (y * z * y⁻¹) := by group
        _ = a := by rw [hya', hSz y hy.1, C.mul_z_mul_z]
    have e : x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹) * x⁻¹ * (y * x⁻¹)⁻¹ := by group
    rw [e]
    exact hH₀ (hcomm x hx _ hyx (Or.inr hyxa))
  refine comm_mem_of_factor (fun s hs q hq => conj_mem_hBig hM D (hSz s hs) hq) inf_le_left
    (fun s hsS => ?_) hcommN
  by_cases hsK : conjSub s K = K
  · exact ⟨s, ⟨hsS, mem_normalizer_of_conjSub_eq hsK⟩, 1, one_mem _, (mul_one s).symm⟩
  · have hsK' : conjSub s K = K' := by
      rcases C25Y.conjSub_pair_of_central hs (hSz s hsS) with ⟨h1, -⟩ | ⟨h1, -⟩
      · exact absurd h1 hsK
      · exact h1
    have hsK'' : conjSub s K' = K := by
      rcases C25Y.conjSub_pair_of_central hs (hSz s hsS) with ⟨h1, -⟩ | ⟨-, h2⟩
      · exact absurd h1 hsK
      · exact h2
    refine ⟨s * τ, ⟨mul_mem hsS hτS, mem_normalizer_of_conjSub_eq ?_⟩, τ⁻¹,
      inv_mem (hH₀ hτH₀), by group⟩
    rw [conjSub_mul, D.τK, hsK'']

end Swaps

end CFSG.ClassicalInvolution.Asc77.C5O
