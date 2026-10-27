module

public import CFSG.ClassicalInvolution.Asc77.AscE187P1b
public import CFSG.ClassicalInvolution.Asc77.AscE187All
public import CFSG.ClassicalInvolution.Asc77.AscE187Delta
public import CFSG.ClassicalInvolution.Asc77.AscE187EndA
public import CFSG.ClassicalInvolution.Asc77.AscE187P1
public import CFSG.ClassicalInvolution.Asc77.Lemma310

public section

namespace CFSG.ClassicalInvolution.Asc77

open CFSG.Open CFSG.ClassicalInvolution.Generic

variable {G : Type} [Group G] [Finite G] {p f : ℕ} [Fact p.Prime] {Ω : Set (Subgroup G)}
  {K : Subgroup G} {S : Sylow 2 G} {R W H : Subgroup G}

theorem E187C.part1_core_of {g : G} (hc : ConjInvariant Ω) (hSH : (S : Subgroup G) ≤ H)
    (hl67 : ∀ (S₁ : Sylow 2 G) (X : Subgroup G), X ∈ RSet Ω → ∀ Y : Subgroup G, Y ∈ RSet Ω →
      X ≤ (S₁ : Subgroup G) → Y ≤ (S₁ : Subgroup G) → X ≠ Y → Commutes X Y)
    (hcc : ∀ {S₁ : Sylow 2 G} {K₁ R₁ T : Subgroup G} {z₁ β : G}, IsUniqueInvolution K₁ z₁ →
      R₁ ∈ RSet Ω → R₁ ≤ K₁ → R₁ ≤ (S₁ : Subgroup G) → β ∈ (S₁ : Subgroup G) → T ∈ RSet Ω →
      T ≤ (S₁ : Subgroup G) → ∀ y ∈ T, y * (β * z₁ * β⁻¹) = (β * z₁ * β⁻¹) * y)
    (hnt : ∀ {x : G}, x ≠ 1 → Subgroup.centralizer ({x} : Set G) ≠ ⊤)
    {K' R' : Subgroup G}
    (hcl : conjSub g K' ∈ twinSet Ω (conjSub g K) → conjSub g K' ≠ conjSub g K →
      conjSub g R' ∈ RSet Ω → conjSub g R' ≤ conjSub g K' →
      conjSub g R' ≤ conjSub g (S : Subgroup G) → ∀ w : G, w ≠ 1 → w * w = 1 →
      IsPGroup 2 (Subgroup.zpowers w) →
      conjSub g R ⊔ conjSub g R' ≤ Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) →
      Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) ≠ ⊤ →
      Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) ≤ conjSub g H)
    (hquat : IsQuatSub R) (hK : K ∈ Ω) (hRR : R ∈ RSet Ω) (hRK : R ≤ K) (hRS : R ≤ (S : Subgroup G))
    (hK'tw : K' ∈ twinSet Ω K) (hne : K' ≠ K) (hR' : R' ∈ RSet Ω) (hR'K' : R' ≤ K')
    (hR'S : R' ≤ (S : Subgroup G)) {z : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hP : ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H) {a t : G} (ha2 : a * a = 1)
    (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (hgH : g ∉ H) (hat : t = g * a * g⁻¹)
    (htS : t ∈ (S : Subgroup G))
    (hCS : ∀ x ∈ (S : Subgroup G), t * x = x * t → x ∈ conjSub g (S : Subgroup G))
    (hWg : ∀ s ∈ conjSub g (S : Subgroup G), conjSub s (conjSub g W) = conjSub g W)
    (habel : ∀ x ∈ conjSub g W, ∀ y ∈ conjSub g W, x * y = y * x)
    (hdel : t * t = 1 → ¬ t * z = z * t →
      ∃ B : Subgroup G, ∃ b : G, B ≤ (S : Subgroup G) ∧ B ≤ Subgroup.centralizer ({t} : Set G) ∧
        IsUniqueInvolution B b ∧ 8 ≤ Nat.card B ∧ b = z * (t * z * t⁻¹) ∧ b ∈ W ∧
        Subgroup.centralizer ({b} : Set G) ≤ H) : False := by
  have ht2 : t * t = 1 := by
    rw [hat]
    calc g * a * g⁻¹ * (g * a * g⁻¹) = g * (a * a) * g⁻¹ := by group
      _ = 1 := by rw [ha2]; group
  have hnc : ¬ t * z = z * t := by
    intro hcomm
    have hmem : g⁻¹ * z * g ∈ Subgroup.centralizer ({a} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have e1 : g⁻¹ * (t * z) * g = a * (g⁻¹ * z * g) := by rw [hat]; group
      have e2 : g⁻¹ * (z * t) * g = (g⁻¹ * z * g) * a := by rw [hat]; group
      rw [← e1, ← e2, hcomm]
    have := hP g⁻¹ (by simpa using haH hmem)
    exact hgH (by simpa using H.inv_mem this)
  obtain ⟨B, b, hBS, hBt, hBb, hB8, hbdef, hbW, hbH⟩ := hdel ht2 hnc
  have hSg : ((conjSylow g S : Sylow 2 G) : Subgroup G) = conjSub g (S : Subgroup G) :=
    coe_conjSylow g S
  have hz₁ : IsUniqueInvolution (conjSub g K) (g * z * g⁻¹) := hz.conj g
  have hz₁W : g * z * g⁻¹ ∈ conjSub g W := conj_mem_conjSub hzW
  have hz₁2 : (g * z * g⁻¹) * (g * z * g⁻¹) = 1 := hz₁.sq
  have hz₁1 : g * z * g⁻¹ ≠ 1 := hz₁.ne_one
  have hBS₁ : ∀ β ∈ B, β ∈ conjSub g (S : Subgroup G) := fun β hβ =>
    hCS β (hBS hβ) (Subgroup.mem_centralizer_singleton_iff.mp (hBt hβ)).symm
  have hBW₁ : ∀ β ∈ B, conjSub β (conjSub g W) = conjSub g W := fun β hβ =>
    hWg β (hBS₁ β hβ)
  have hbz : ¬ b * (g * z * g⁻¹) = (g * z * g⁻¹) * b := by
    intro hcomm
    have : g * z * g⁻¹ ∈ Subgroup.centralizer ({b} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hcomm.symm
    exact hgH (hP g (hbH this))
  have hBp : IsPGroup 2 B := S.isPGroup'.to_le hBS
  obtain ⟨E, u, v, hEdef, hEW, hEsq, huE, hvE, hu1, hv1, huv, hbu, hbv⟩ :=
    exists_pair_in_E hBp hBb hB8 habel hBW₁ hz₁W hz₁2 hz₁1 hbz
  have hK₁ : conjSub g K ∈ Ω := hc g K hK
  have hR₁ : conjSub g R ∈ RSet Ω := RSet.conj hc hRR g
  have hR₁K₁ : conjSub g R ≤ conjSub g K := conjSub_mono hRK
  have hR₁S : conjSub g R ≤ conjSub g (S : Subgroup G) := conjSub_mono hRS
  have hR₁' : conjSub g R' ∈ RSet Ω := RSet.conj hc hR' g
  have hR₁'K : conjSub g R' ≤ conjSub g K' := conjSub_mono hR'K'
  have hR₁'S : conjSub g R' ≤ conjSub g (S : Subgroup G) := conjSub_mono hR'S
  have hEcent : ∀ T ∈ RSet Ω, T ≤ conjSub g (S : Subgroup G) → ∀ w ∈ E, ∀ y ∈ T,
      y * w = w * y := by
    intro T hT hTS w hw y hy
    have hle : E ≤ Subgroup.centralizer (T : Set G) := by
      rw [hEdef]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨β, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      exact hcc (S₁ := conjSylow g S) hz₁ hR₁ hR₁K₁
        (by rw [hSg]; exact hR₁S) (by rw [hSg]; exact hBS₁ β β.2) hT (by rw [hSg]; exact hTS) y hy
    exact Subgroup.mem_centralizer_iff.mp (hle hw) y hy
  have hK₁tw : conjSub g K' ∈ twinSet Ω (conjSub g K) := twinSet_conj hc hK'tw g
  have hne₁ : conjSub g K' ≠ conjSub g K := fun h' => hne ((conjSub_inj g).mp h')
  have hEx : ∀ w ∈ E, w ≠ 1 → Subgroup.centralizer ({w} : Set G) ≤ conjSub g H := by
    intro w hw hw1
    have hw2 : w * w = 1 := hEsq w hw
    have hA2 : IsPGroup 2 (Subgroup.zpowers w) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, orderOf_eq_two_of_sq hw1 hw2]; norm_num)
    have hc1 : conjSub g R ≤ Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq_singleton]
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hEcent _ hR₁ hR₁S w hw y hy
    have hc2 : conjSub g R' ≤ Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
      rw [centralizer_zpowers_eq_singleton]
      intro y hy
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact hEcent _ hR₁' hR₁'S w hw y hy
    have hXne : Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) ≠ ⊤ := by
      rw [centralizer_zpowers_eq_singleton]
      exact hnt hw1
    have := hcl hK₁tw hne₁ hR₁' hR₁'K hR₁'S w hw1 hw2 hA2 (sup_le hc1 hc2) hXne
    rwa [centralizer_zpowers_eq_singleton] at this
  have hW₁ab : ∀ x ∈ conjSub g W, ∀ y ∈ conjSub g W, x * y = y * x := habel
  have huv' : u * v = v * u := hW₁ab u (hEW huE) v (hEW hvE)
  set U : Subgroup G := Subgroup.closure ({u, v} : Set G) with hU
  have hUE : U ≤ E := (Subgroup.closure_le E).mpr (by
    intro x hx
    rcases hx with rfl | rfl
    exacts [huE, hvE])
  have hUH : U ≤ H := (Subgroup.closure_le H).mpr (by
    intro x hx
    rcases hx with rfl | rfl
    · exact hbH (Subgroup.mem_centralizer_singleton_iff.mpr hbu.symm)
    · exact hbH (Subgroup.mem_centralizer_singleton_iff.mpr hbv.symm))
  have hUp : IsPGroup 2 U := fun g' => ⟨1, by
    apply Subtype.ext
    have := hEsq g' (hUE g'.2)
    simpa [pow_two] using this⟩
  obtain ⟨h₀, hh₀H, hUh₀⟩ := exists_conj_sylow_ge hSH hUp hUH
  have hS'2 : IsPGroup 2 (conjSub h₀ (S : Subgroup G)) := isPGroup_conjSub h₀ S.isPGroup'
  set Δ : Set (Subgroup G) := {X | X ∈ RSet Ω ∧ X ≤ conjSub h₀ (S : Subgroup G)} with hΔ
  have hΔinv : ∀ X ∈ Δ, ∀ s ∈ conjSub h₀ (S : Subgroup G), conjSub s X ∈ Δ := by
    intro X hX s hs
    refine ⟨RSet.conj hc hX.1 s, fun x hx => ?_⟩
    rw [mem_conjSub_iff] at hx
    have h1 : s⁻¹ * x * s ∈ conjSub h₀ (S : Subgroup G) := hX.2 hx
    have h2 : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
    rw [h2]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hs h1) (Subgroup.inv_mem _ hs)
  have hΔcomm : ∀ X ∈ Δ, ∀ Y ∈ Δ, X ≠ Y → Commutes X Y := fun X hX Y hY hXY =>
    hl67 (conjSylow h₀ S) X hX.1 Y hY.1 (by rw [coe_conjSylow]; exact hX.2)
      (by rw [coe_conjSylow]; exact hY.2) hXY
  have hX₀ : conjSub h₀ R ∈ Δ := ⟨RSet.conj hc hRR h₀, conjSub_mono hRS⟩
  have hΦ : ∃ x ∈ conjSub h₀ R, x * x ≠ 1 ∨ ∃ y ∈ conjSub h₀ R, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hquat.exists_not_commute
    refine ⟨h₀ * x * h₀⁻¹, conj_mem_conjSub hx, Or.inr ⟨h₀ * y * h₀⁻¹, conj_mem_conjSub hy, ?_⟩⟩
    intro h'
    apply hxy
    have e1 : h₀ * (x * y) * h₀⁻¹ = (h₀ * x * h₀⁻¹) * (h₀ * y * h₀⁻¹) := by group
    have e2 : h₀ * (y * x) * h₀⁻¹ = (h₀ * y * h₀⁻¹) * (h₀ * x * h₀⁻¹) := by group
    have := e1.trans (h'.trans e2.symm)
    have h3 := mul_left_cancel (mul_right_cancel this)
    exact h3
  have h310 := lemma_3_10 hS'2 (fun X hX => hX.2) hΔinv hΔcomm
    (hUh₀ (Subgroup.subset_closure (by simp))) (hUh₀ (Subgroup.subset_closure (by simp)))
    hu1 hv1 huv (hEsq u huE) (hEsq v hvE) huv' hX₀ hΦ
  have hΓ : gamma1 U (conjSub h₀ (S : Subgroup G)) ≤ conjSub g H := by
    unfold gamma1
    refine iSup₂_le fun w hw => iSup_le fun hw1 => ?_
    exact inf_le_right.trans (hEx w (hUE hw) hw1)
  obtain ⟨⟨w, hw⟩, hw1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h310
  have hw1' : w ≠ 1 := fun h' => hw1 (Subtype.ext h')
  have hwR : w ∈ conjSub h₀ R := hw.2
  have hz' : IsUniqueInvolution (conjSub h₀ K) (h₀ * z * h₀⁻¹) := hz.conj h₀
  have hR2 : IsPGroup 2 R := by
    obtain ⟨J, -, -, h2, -⟩ := mem_RSet_iff.mp hRR
    exact h2
  have hw2 : IsPGroup 2 (Subgroup.zpowers w) :=
    (isPGroup_conjSub h₀ hR2).to_le (Subgroup.zpowers_le.mpr hwR)
  have hz'mem : h₀ * z * h₀⁻¹ ∈ Subgroup.zpowers w :=
    mem_zpowers_of_isUniqueInvolution hz' (conjSub_mono hRK hwR) hw1' hw2
  have hz'Γ : h₀ * z * h₀⁻¹ ∈ gamma1 U (conjSub h₀ (S : Subgroup G)) :=
    (Subgroup.zpowers_le.mpr hw : Subgroup.zpowers w ≤ _ ⊓ _) hz'mem |>.1
  have hz'H : g⁻¹ * (h₀ * z * h₀⁻¹) * g ∈ H := by
    have := hΓ hz'Γ
    rwa [mem_conjSub_iff] at this
  have hxH := hP (g⁻¹ * h₀) (by
    have e : g⁻¹ * h₀ * z * (g⁻¹ * h₀)⁻¹ = g⁻¹ * (h₀ * z * h₀⁻¹) * g := by group
    rw [e]
    exact hz'H)
  apply hgH
  have : g⁻¹ ∈ H := by
    have e : g⁻¹ = (g⁻¹ * h₀) * h₀⁻¹ := by group
    rw [e]
    exact H.mul_mem hxH (H.inv_mem hh₀H)
  simpa using H.inv_mem this

theorem MinCex.part1_core (h : E187Hyps p f) (h4 : E187E4C p f)
    (c : MinCex p f Ω K S R W H) {z : G} (hz : IsUniqueInvolution K z) (hzW : z ∈ W)
    (hP : ∀ x : G, x * z * x⁻¹ ∈ H → x ∈ H) {a g t : G} (ha2 : a * a = 1)
    (haH : Subgroup.centralizer ({a} : Set G) ≤ H) (hgH : g ∉ H) (hat : t = g * a * g⁻¹)
    (htS : t ∈ (S : Subgroup G))
    (hCS : ∀ x ∈ (S : Subgroup G), t * x = x * t → x ∈ conjSub g (S : Subgroup G)) : False := by
  have hp : p ≠ 2 := c.stand.odd
  have hq : 5 ≤ p ^ f := c.stand.five
  have hΩ : HypOmegaMod p f Ω := c.stand.hyp
  have hA : EtaAbelian Ω := h.etaAbelian hp hq hΩ
  have c₁ := c.conj g
  obtain ⟨K', hK'tw, hne, R', hR', hR'K', hR'S⟩ := c.stand.twin
  obtain ⟨hRR, hRK, hRS⟩ := c.stand.hR
  exact E187C.part1_core_of (g := g) (K' := K') (R' := R') hΩ.conjInvariant (c.sylow_le hA)
    (fun S₁ X hX Y hY hXS hYS hXY => h.l67 hp hq G Ω hΩ S₁ X hX Y hY hXS hYS hXY)
    (fun hz₁ hR₁ hR₁K₁ hR₁S hβ hT hTS =>
      centralizes_conj_of_mem_RSet h hp hq hΩ hz₁ hR₁ hR₁K₁ hR₁S hβ hT hTS)
    (fun hw1 => c.centralizer_ne_top h.e6 hw1)
    (fun hK₁tw hne₁ hR₁' hR₁'K hR₁'S w hw1 hw2 hA2 hsup hXne =>
      c₁.centralizer_le_H h4 hK₁tw hne₁ hR₁' hR₁'K (by rw [coe_conjSylow]; exact hR₁'S) hA2 hsup
        hXne)
    (hΩ.isQuatSub_of_mem_RSet hp hRR) c.stand.mem hRR hRK hRS hK'tw hne hR' hR'K' hR'S hz hzW hP
    ha2 haH hgH hat htS hCS
    (fun s hs => c₁.stand.hW.2.2 s (by rw [coe_conjSylow]; exact hs))
    (by obtain ⟨η, -, -, -, habel, -⟩ := c₁.exists_eta hA; exact habel)
    (fun ht2 hnc => c.exists_delta h hz hzW ht2 htS hnc)

end CFSG.ClassicalInvolution.Asc77
