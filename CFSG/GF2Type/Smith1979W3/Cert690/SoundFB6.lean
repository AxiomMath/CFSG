module

public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB6a
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB3
public import CFSG.GF2Type.Smith1979W3.Cert690.SoundFB5

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.GF2Type.Smith1979W3.Cert690

open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.O62 Module

theorem pglF4Of_facts {D : PGLData} (h : pglF4Of D = true) :
    (∀ i (hi : i < D.elems0.size), D.elems0[i]'hi ∈ D.elems) ∧
    (∀ x ∈ kPGL0Gens, ∀ g ∈ kPGLGens,
      Code.mul g (D.invMap.getD g 0) = Code.one ∧
        Code.mul (Code.mul g x) (D.invMap.getD g 0) ∈ D.elems0) ∧
    (∀ g ∈ kPGLGens, ∀ h ∈ kPGLGens,
      Code.mul g (D.invMap.getD g 0) = Code.one ∧
        Code.mul h (D.invMap.getD h 0) = Code.one ∧
          Code.mul (Code.mul (Code.mul g h) (D.invMap.getD g 0)) (D.invMap.getD h 0)
            ∈ D.elems0) ∧
    D.commWit.size = kPGL0Gens.length ∧
    (∀ j, j < kPGL0Gens.length → ∃ i x, i < D.elems.size ∧ x < D.elems.size ∧
      Code.mul (Code.mul (Code.mul (D.elems[i]!) (D.elems[x]!)) (D.invs[i]!)) (D.invs[x]!) =
        kPGL0Gens[j]!) := by
  simp only [pglF4Of, Array.all_eq_true, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hsub, hnorm⟩, hcomm⟩, hsize⟩, hwit⟩ := h
  refine ⟨?_, ?_, ?_, hsize, ?_⟩
  · intro i hi
    exact Array.contains_iff_mem.mp (hsub i hi)
  · intro x hx g hg
    exact ⟨(hnorm x hx g hg).1, Array.contains_iff_mem.mp (hnorm x hx g hg).2⟩
  · intro g hg h hh
    exact ⟨(hcomm g hg h hh).1.1, (hcomm g hg h hh).1.2,
      Array.contains_iff_mem.mp (hcomm g hg h hh).2⟩
  · intro j hj
    have hw := hwit j (List.mem_range.mpr hj)
    cases hc : D.commWit[j]! with
    | none =>
      rw [hc] at hw
      exact absurd hw (by simp)
    | some p =>
      obtain ⟨i, x⟩ := p
      rw [hc] at hw
      rw [Bool.and_eq_true, Bool.and_eq_true] at hw
      obtain ⟨⟨hi', hx'⟩, heq'⟩ := hw
      exact ⟨i, x, of_decide_eq_true hi', of_decide_eq_true hx', beq_iff_eq.mp heq'⟩

theorem pglF13Of_facts {D : PGLData} (h : pglF13Of D = true) :
    ∀ i (hi : i < (D.elems0.filter fun w =>
        w != Code.one && Code.mul w w == Code.one).size),
      (D.elems.filter (fun k =>
          Code.mul k ((D.elems0.filter fun w =>
            w != Code.one && Code.mul w w == Code.one)[i]'hi) ==
            Code.mul ((D.elems0.filter fun w =>
              w != Code.one && Code.mul w w == Code.one)[i]'hi) k)).size = 16 ∧
        ((List.range 64).filter (fun v =>
          Code.act ((D.elems0.filter fun w =>
            w != Code.one && Code.mul w w == Code.one)[i]'hi) v == v)).length = 16 := by
  simp only [pglF13Of, Array.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  exact h

theorem KPGL0_le_KPGL_of_check (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (h : pglFactsCheck () = true) :
    KPGL0 ≤ KPGL := by
  obtain ⟨-, -, -, h4, -, -, -, -, -, -, -, -, -⟩ := pglFactsCheck_all h
  have hsub := (pglF4Of_facts h4).1
  intro w hw
  have hc_mem : hK0.code w ∈ (pglData ()).elems0.toList := hK0.code_mem hw
  have hc_mem' : hK0.code w ∈ (pglData ()).elems0 := Array.mem_toList_iff.mp hc_mem
  obtain ⟨i, hi, hieq⟩ := Array.mem_iff_getElem.mp hc_mem'
  have hsubi : (pglData ()).elems0[i] ∈ (pglData ()).elems := hsub i hi
  rw [hieq] at hsubi
  exact (mem_KPGL_iff_of_enum hK (hK0.hasCode_code hw) (hK0.lt _ hc_mem)).2 hsubi

theorem pglF13_sound_of (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (h : pglFactsCheck () = true) :
    ∀ w ∈ KPGL0, w ≠ 1 → w * w = 1 →
      Nat.card ↥(KPGL ⊓ Subgroup.centralizer {w}) = 16 ∧
        Nat.card {v : V₀ // w v = v} = 16 := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, h13⟩ := pglFactsCheck_all h
  have hK0K : KPGL0 ≤ KPGL := KPGL0_le_KPGL_of_check hK hK0 h
  have h13f := pglF13Of_facts h13
  intro w hw hw1 hw2
  have hc_mem : hK0.code w ∈ (pglData ()).elems0.toList := hK0.code_mem hw
  have hcne : hK0.code w ≠ Code.one := by
    intro hc
    have : hK0.elem (hK0.code w) = hK0.elem Code.one := by rw [hc]
    have h1 : hK0.elem Code.one = 1 := by
      rw [← hK0.code_one]
      exact hK0.elem_code (Subgroup.one_mem _)
    exact hw1 (by rw [hK0.elem_code hw] at this; exact this.trans h1)
  have hmulc : Code.mul (hK0.code w) (hK0.code w) = Code.one := by
    have h1 : hK0.code (w * w) = Code.mul (hK0.code w) (hK0.code w) :=
      hK0.code_mul hw hw
    rw [hw2] at h1
    exact h1.symm.trans hK0.code_one
  have hinv : isInvCode (hK0.code w) = true := by
    simp [isInvCode, hcne, hmulc]
  have hfilt_mem : hK0.code w ∈ ((pglData ()).elems0.filter fun w =>
      w != Code.one && Code.mul w w == Code.one).toList := by
    rw [Array.mem_toList_iff, Array.mem_filter]
    exact ⟨Array.mem_toList_iff.mp hc_mem, by simp [hcne, hmulc]⟩
  rw [Array.mem_toList_iff] at hfilt_mem
  obtain ⟨i, hi, hieq⟩ := Array.mem_iff_getElem.mp hfilt_mem
  have hcounts := h13f i hi
  rw [hieq] at hcounts
  have hcode_eq : hK.code w = hK0.code w :=
    Code.HasCode.code_eq (hK.hasCode_code (hK0K hw)) (hK0.hasCode_code hw)
      (hK.lt _ (hK.code_mem (hK0K hw))) (hK0.lt _ hc_mem)
  constructor
  · rw [natCard_centralizer_filter hK (hK0K hw), hcode_eq]
    exact hcounts.1
  · rw [natCard_fixed_filter hK (hK0K hw), hcode_eq]
    exact hcounts.2

theorem pglF12Of_facts {D : PGLData} (h : pglF12Of D = true) :
    pglInvolutionsOK D = true ∧ pglOutersOK D = true ∧ D.outers.size ≠ 0 ∧
      D.w12.size = D.outers.size ∧
      (∀ j, j < D.outers.size → D.w12[j]! < D.elems.size ∧
        Code.mul (Code.mul (D.elems[D.w12[j]!]!) (D.outers[0]!)) (D.invs[D.w12[j]!]!) =
          D.outers[j]!) := by
  simp only [pglF12Of, Array.all_eq_true, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, bne_iff_ne] at h
  obtain ⟨⟨⟨⟨hInv, hOut⟩, hne⟩, hsize⟩, hwit⟩ := h
  refine ⟨hInv, hOut, hne, hsize, ?_⟩
  intro j hj
  exact hwit j (List.mem_range.mpr hj)

theorem isInvCode_code_of_involution {D : PGLData} (hK : EnumCert kPGLGens D.elems.toList)
    {u : V₀ ≃ₗ[ZMod 2] V₀} (hu : u ∈ KPGL) (hu1 : u ≠ 1) (hu2 : u * u = 1) :
    isInvCode (hK.code u) = true := by
  have hc_mem : hK.code u ∈ D.elems.toList := hK.code_mem hu
  have hcne : hK.code u ≠ Code.one := by
    intro hc
    have h1 : hK.elem (hK.code u) = hK.elem Code.one := by rw [hc]
    have h2 : hK.elem Code.one = 1 := by
      rw [← hK.code_one]
      exact hK.elem_code (Subgroup.one_mem _)
    exact hu1 (by rw [hK.elem_code hu] at h1; exact h1.trans h2)
  have hmul : Code.mul (hK.code u) (hK.code u) = Code.one := by
    have h1 : hK.code (u * u) = Code.mul (hK.code u) (hK.code u) := hK.code_mul hu hu
    rw [hu2] at h1
    exact h1.symm.trans hK.code_one
  simp [isInvCode, hcne, hmul]

theorem pglF12_sound_of (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (h : pglFactsCheck () = true) :
    ∀ u ∈ KPGL, u ∉ KPGL0 → u * u = 1 → ∀ u' ∈ KPGL, u' ∉ KPGL0 → u' * u' = 1 →
      ∃ k ∈ KPGL, k * u * k⁻¹ = u' := by
  obtain ⟨h1, -, -, -, -, -, -, -, -, -, -, h12, -⟩ := pglFactsCheck_all h
  obtain ⟨⟨-, -⟩, hinv, -⟩ := pglF1Of_facts h1
  obtain ⟨hInvOK, hOutOK, hOutNe, -, hW12⟩ := pglF12Of_facts h12
  have hpos : 0 < (pglData ()).outers.size := Nat.pos_of_ne_zero hOutNe
  have hout_mem : ∀ j, j < (pglData ()).outers.size →
      (pglData ()).outers[j]! ∈ (pglData ()).elems.toList := by
    intro j hj
    have hmemA : (pglData ()).outers[j]! ∈ (pglData ()).outers := by
      rw [array_getElem!_eq_getElem_of_lt hj]
      exact Array.mem_toList_iff.mp (Array.getElem_mem_toList hj)
    exact Array.mem_toList_iff.mpr (mem_outers_iff_of_ok hOutOK |>.mp hmemA).1
  let U0 : V₀ ≃ₗ[ZMod 2] V₀ := hK.elem ((pglData ()).outers[0]!)
  have hU0mem : U0 ∈ KPGL := hK.elem_mem (hout_mem 0 hpos)
  have hconj : ∀ j (hj : j < (pglData ()).outers.size),
      ∃ k ∈ KPGL, k * (hK.elem ((pglData ()).outers[j]!)) * k⁻¹ = U0 := by
    intro j hj
    let i := (pglData ()).w12[j]!
    have hi : i < (pglData ()).elems.size := (hW12 j hj).1
    have hmul := (hW12 j hj).2
    let G : V₀ ≃ₗ[ZMod 2] V₀ := hK.elem ((pglData ()).elems[i]!)
    have hex : ∃ H : V₀ ≃ₗ[ZMod 2] V₀,
        Code.HasCode (H : V₀ →ₗ[ZMod 2] V₀) ((pglData ()).invs[i]!) :=
      exists_equiv_of_mul_eq_one (EnumCert.code_mul_comm_one (hinv i hi))
    let H : V₀ ≃ₗ[ZMod 2] V₀ := Classical.choose hex
    have hHcode : Code.HasCode (H : V₀ →ₗ[ZMod 2] V₀) ((pglData ()).invs[i]!) :=
      Classical.choose_spec hex
    have hi_mem : (pglData ()).elems[i]! ∈ (pglData ()).elems.toList := by
      rw [array_getElem!_eq_getElem_of_lt hi]
      exact Array.getElem_mem_toList hi
    have hGcode : Code.HasCode (G : V₀ →ₗ[ZMod 2] V₀) ((pglData ()).elems[i]!) :=
      hK.hasCode_elem hi_mem
    have hGH : G * H = 1 := by
      apply Code.HasCode.eq_of_equiv (hGcode.mul hHcode)
      rw [hinv i hi]
      exact Code.hasCode_one
    have hHinv : H = G⁻¹ := eq_inv_of_mul_eq_one_right hGH
    have hGmem : G ∈ KPGL := hK.elem_mem hi_mem
    have hU0code : Code.HasCode (U0 : V₀ →ₗ[ZMod 2] V₀) ((pglData ()).outers[0]!) :=
      hK.hasCode_elem (hout_mem 0 hpos)
    have hUjcode : Code.HasCode (hK.elem ((pglData ()).outers[j]!) : V₀ →ₗ[ZMod 2] V₀)
        ((pglData ()).outers[j]!) := hK.hasCode_elem (hout_mem j hj)
    have hcodeL : Code.HasCode (((G * U0) * H : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
        (Code.mul (Code.mul ((pglData ()).elems[i]!) ((pglData ()).outers[0]!))
          ((pglData ()).invs[i]!)) := (hGcode.mul hU0code).mul hHcode
    have hUj : (G * U0) * H = hK.elem ((pglData ()).outers[j]!) := by
      rw [hmul] at hcodeL
      exact hcodeL.eq_of_equiv hUjcode
    rw [hHinv] at hUj
    refine ⟨G⁻¹, Subgroup.inv_mem (H := KPGL) hGmem, ?_⟩
    calc G⁻¹ * hK.elem ((pglData ()).outers[j]!) * G
          = G⁻¹ * ((G * U0) * G⁻¹) * G := by rw [hUj]
        _ = U0 := by group
  have hbase : ∀ u ∈ KPGL, u ∉ KPGL0 → u * u = 1 →
      ∃ k ∈ KPGL, k * u * k⁻¹ = U0 := by
    intro u hu hu0 hu2
    have hc_out : hK.code u ∈ (pglData ()).outers := by
      apply (mem_outers_iff_of_ok hOutOK).mpr
      refine ⟨Array.mem_toList_iff.mp (hK.code_mem hu), ?_, ?_⟩
      · have hu1 : u ≠ 1 := by
          intro h
          exact hu0 (by rw [h]; exact Subgroup.one_mem _)
        exact isInvCode_code_of_involution hK hu hu1 hu2
      · intro hc0
        exact hu0 ((mem_KPGL0_iff_of_enum hK0 (hK.hasCode_code hu)
          (hK.lt _ (hK.code_mem hu))).2 hc0)
    obtain ⟨j, hj, hjeq⟩ := Array.mem_iff_getElem.mp hc_out
    obtain ⟨k, hk, hconjk⟩ := hconj j hj
    refine ⟨k, hk, ?_⟩
    have hUjeq : hK.elem ((pglData ()).outers[j]!) = u := by
      rw [array_getElem!_eq_getElem_of_lt hj, hjeq]
      exact hK.elem_code hu
    rw [← hUjeq]
    exact hconjk
  intro u hu hu0 hu2 u' hu' hu'0 hu'2
  obtain ⟨k1, hk1, hk1c⟩ := hbase u hu hu0 hu2
  obtain ⟨k2, hk2, hk2c⟩ := hbase u' hu' hu'0 hu'2
  refine ⟨k2⁻¹ * k1, Subgroup.mul_mem (H := KPGL) (Subgroup.inv_mem (H := KPGL) hk2) hk1, ?_⟩
  calc (k2⁻¹ * k1) * u * (k2⁻¹ * k1)⁻¹
      = k2⁻¹ * (k1 * u * k1⁻¹) * k2 := by group
    _ = k2⁻¹ * U0 * k2 := by rw [hk1c]
    _ = u' := by
      have h := congrArg (fun x => k2⁻¹ * x * k2) hk2c
      calc k2⁻¹ * U0 * k2 = k2⁻¹ * (k2 * u' * k2⁻¹) * k2 := by rw [hk2c]
        _ = u' := by group

theorem pglF9Of_facts {D : PGLData} (h : pglF9Of D = true) :
    (List.filter (fun v => v != 0) (vPlusVecs ++ vStarVecs)).contains 2 = true ∧
      D.w9.size = 64 ∧
      (∀ x ∈ List.filter (fun v => v != 0) (vPlusVecs ++ vStarVecs),
        D.w9[x]! < D.elems.size ∧ Code.act (D.elems[D.w9[x]!]!) 2 = x) := by
  simp only [pglF9Of, Array.all_eq_true, List.all_eq_true, Bool.and_eq_true, beq_iff_eq,
    decide_eq_true_eq, bne_iff_ne] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨h1, h2, h3⟩

theorem pglF9_sound_of (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (h : pglFactsCheck () = true) :
    ∀ e e' : V₀, e ≠ 0 → e' ≠ 0 → (e ∈ VPlus ∨ e ∈ VStar) →
      (e' ∈ VPlus ∨ e' ∈ VStar) → ∃ k ∈ KPGL, k e = e' := by
  obtain ⟨-, -, -, -, -, -, -, -, h9, -, -, -, -⟩ := pglFactsCheck_all h
  obtain ⟨-, -, h9f⟩ := pglF9Of_facts h9
  let vs := List.filter (fun v => v != 0) (vPlusVecs ++ vStarVecs)
  have key_code : ∀ n ∈ vs, ∃ K ∈ KPGL, K (Code.vec 2) = Code.vec n := by
    intro n hn
    let i := (pglData ()).w9[n]!
    have hi : i < (pglData ()).elems.size := (h9f n hn).1
    have hi_mem : (pglData ()).elems[i]! ∈ (pglData ()).elems.toList := by
      rw [array_getElem!_eq_getElem_of_lt hi]
      exact Array.getElem_mem_toList hi
    let K : V₀ ≃ₗ[ZMod 2] V₀ := hK.elem ((pglData ()).elems[i]!)
    have hKmem : K ∈ KPGL := hK.elem_mem hi_mem
    refine ⟨K, hKmem, ?_⟩
    change (K : V₀ →ₗ[ZMod 2] V₀) (Code.vec 2) = Code.vec n
    rw [show (K : V₀ →ₗ[ZMod 2] V₀) (Code.vec 2) =
        Code.vec (Code.act ((pglData ()).elems[i]!) 2) from
      apply_vec_of_hasCode (hK.hasCode_elem hi_mem) 2]
    rw [(h9f n hn).2]
  have key : ∀ e, e ≠ 0 → (e ∈ VPlus ∨ e ∈ VStar) → ∃ K ∈ KPGL, K (Code.vec 2) = e := by
    intro e he hev
    rcases hev with heP | heS
    · rw [mem_VPlus_iff] at heP
      obtain ⟨n, hn, rfl⟩ := heP
      have hn0 : n ≠ 0 := by intro h0; exact he (by rw [h0, vec_zero])
      have hvs : n ∈ vs := by
        rw [List.mem_filter]
        exact ⟨List.mem_append_left _ hn, by simpa [bne_iff_ne] using hn0⟩
      exact key_code n hvs
    · rw [mem_VStar_iff] at heS
      obtain ⟨n, hn, rfl⟩ := heS
      have hn0 : n ≠ 0 := by intro h0; exact he (by rw [h0, vec_zero])
      have hvs : n ∈ vs := by
        rw [List.mem_filter]
        exact ⟨List.mem_append_right _ hn, by simpa [bne_iff_ne] using hn0⟩
      exact key_code n hvs
  rintro e e' he he' hev hev'
  obtain ⟨Ke, hKe, heK⟩ := key e he hev
  obtain ⟨Ke', hKe', heK'⟩ := key e' he' hev'
  refine ⟨Ke' * Ke⁻¹, Subgroup.mul_mem (H := KPGL) hKe' (Subgroup.inv_mem (H := KPGL) hKe), ?_⟩
  rw [LinearEquiv.mul_apply, ← heK]
  have hcomp : Ke⁻¹ (Ke (Code.vec 2)) = Code.vec 2 := by simp
  rw [hcomp]
  exact heK'

theorem pglF8Of_facts {D : PGLData} (h : pglF8Of D = true) :
    ∀ n, n < 64 → n ≠ 0 →
      let B := spanArr ((D.elems0.map fun k => Code.act k n).toList)
      (B.size = 8 ∧ sameSet B vPlusVecs = true) ∨
        (B.size = 8 ∧ sameSet B vStarVecs = true) ∨ B.size = 64 := by
  simp only [pglF8Of, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  intro n hn hn0
  have h' := h n (List.mem_range.mpr hn)
  rw [if_neg (by simpa using hn0)] at h'
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h'
  rcases h' with hAB' | h64
  · rcases hAB' with hAB | hA'B'
    · exact Or.inl hAB
    · exact Or.inr (Or.inl hA'B')
  · exact Or.inr (Or.inr h64)

theorem Code.act_one_of_lt {m : ℕ} (hm : m < 64) : Code.act Code.one m = m := by
  apply vec_injective_of_lt (Code.act_lt _ _) hm
  rw [Code.vec_act, Code.mat_one, Matrix.one_mulVec]

theorem orbit_span_trichotomy {D : PGLData} (hK0 : EnumCert kPGL0Gens D.elems0.toList)
    (h8 : pglF8Of D = true) {n : ℕ} (hn : n < 64) (hn0 : n ≠ 0) :
    let S := (D.elems0.map fun k => Code.act k n).toList
    spanOfList S = VPlus ∨ spanOfList S = VStar ∨ spanOfList S = ⊤ := by
  classical
  let S := (D.elems0.map fun k => Code.act k n).toList
  let B := spanArr S
  have hSlt : ∀ x ∈ S, x < 64 := by
    intro x hx
    rw [show S = (D.elems0.map fun k => Code.act k n).toList from rfl] at hx
    rw [Array.mem_toList_iff] at hx
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
    simp only [Array.getElem_map]
    exact Code.act_lt _ _
  have h8f := pglF8Of_facts h8 n hn hn0
  change (B.size = 8 ∧ sameSet B vPlusVecs = true) ∨
    (B.size = 8 ∧ sameSet B vStarVecs = true) ∨ B.size = 64 at h8f
  have hspanB : spanOfList B.toList = spanOfList S := by
    dsimp [B]
    exact spanOfList_spanArr S
  rcases h8f with ⟨-, hsame⟩ | ⟨-, hsame⟩ | hsize
  · left
    rw [← hspanB, spanOfList_eq_of_sameSet hsame, spanOfList_vPlus]
  · right; left
    rw [← hspanB, spanOfList_eq_of_sameSet hsame, spanOfList_vStar]
  · right; right
    rw [eq_top_iff]
    intro v _
    obtain ⟨m, hm, rfl⟩ := exists_vec v
    have hnodup : B.toList.Nodup := by
      dsimp [B]
      exact spanArr_nodup S hSlt
    have hlt : ∀ b ∈ B.toList, b < 64 := by
      dsimp [B]
      exact spanArr_lt S hSlt
    have hcard : B.toList.toFinset.card = 64 := by
      rw [List.toFinset_card_of_nodup hnodup]
      have : B.toList.length = 64 := by simpa [Array.length_toList] using hsize
      exact this
    have hsub : B.toList.toFinset ⊆ Finset.range 64 := by
      intro x hx
      rw [List.mem_toFinset] at hx
      exact Finset.mem_range.mpr (hlt x hx)
    have heq : B.toList.toFinset = Finset.range 64 :=
      Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; simp)
    have hmlist : m ∈ B.toList := by
      have : m ∈ B.toList.toFinset := by
        rw [heq]
        exact Finset.mem_range.mpr hm
      simpa using this
    exact (spanArr_represents S).1 m (by simpa [B] using hmlist)

theorem vec_mem_orbit_span {D : PGLData} (hK0 : EnumCert kPGL0Gens D.elems0.toList)
    {m : ℕ} (hm : m < 64) :
    Code.vec m ∈ spanOfList ((D.elems0.map fun k => Code.act k m).toList) := by
  have hone_arr : Code.one ∈ D.elems0 := Array.mem_toList_iff.mp hK0.one_mem
  obtain ⟨i, hi, hieq⟩ := Array.mem_iff_getElem.mp hone_arr
  have hmS : m ∈ (D.elems0.map fun k => Code.act k m).toList := by
    rw [Array.mem_toList_iff]
    refine Array.mem_iff_getElem.mpr ⟨i, by simpa using hi, ?_⟩
    simp only [Array.getElem_map]
    rw [hieq, Code.act_one_of_lt hm]
  exact Submodule.subset_span ⟨m, hmS, rfl⟩

theorem orbit_span_le_of_invariant {D : PGLData} (hK0 : EnumCert kPGL0Gens D.elems0.toList)
    {W : Submodule (ZMod 2) V₀}
    (hWinv : ∀ k ∈ KPGL0, ∀ w ∈ W, k w ∈ W) {n : ℕ} (hnW : Code.vec n ∈ W) :
    let S := (D.elems0.map fun k => Code.act k n).toList
    spanOfList S ≤ W := by
  intro S
  rw [spanOfList, Submodule.span_le]
  rintro v ⟨x, hx, rfl⟩
  dsimp only [S] at hx
  simp only [Set.mem_setOf_eq] at hx
  rw [Array.mem_toList_iff] at hx
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp hx
  have hi0 : i < D.elems0.size := by simpa using hi
  have hi_mem : D.elems0[i]! ∈ D.elems0.toList := by
    rw [array_getElem!_eq_getElem_of_lt hi0]
    exact Array.getElem_mem_toList hi0
  let k : V₀ ≃ₗ[ZMod 2] V₀ := hK0.elem (D.elems0[i]!)
  have hkmem : k ∈ KPGL0 := hK0.elem_mem hi_mem
  have hkw : k (Code.vec n) ∈ W := hWinv k hkmem (Code.vec n) hnW
  rw [show k (Code.vec n) = Code.vec (Code.act (D.elems0[i]!) n) from
    apply_vec_of_hasCode (hK0.hasCode_elem hi_mem) n] at hkw
  rw [Array.getElem_map]
  rw [array_getElem!_eq_getElem_of_lt hi0] at hkw
  exact hkw

theorem pglF8_sound_of (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (h : pglFactsCheck () = true) :
    ∀ W : Submodule (ZMod 2) V₀, (∀ k ∈ KPGL0, ∀ w ∈ W, k w ∈ W) →
      W = ⊥ ∨ W = VPlus ∨ W = VStar ∨ W = ⊤ := by
  obtain ⟨-, -, -, -, h5, -, -, h8, -, -, -, -, -⟩ := pglFactsCheck_all h
  intro W hW
  by_cases hbot : W = ⊥
  · exact Or.inl hbot
  · right
    obtain ⟨w, hwW, hw0⟩ := (Submodule.ne_bot_iff W).mp hbot
    obtain ⟨n, hn, rfl⟩ := exists_vec w
    have hn0 : n ≠ 0 := by intro h0; exact hw0 (by rw [h0, vec_zero])
    have htri := orbit_span_trichotomy hK0 h8 hn hn0
    have hle := orbit_span_le_of_invariant hK0 hW (n := n) hwW
    rcases htri with hVP | hVS | hTop
    · have hVPW : VPlus ≤ W := hVP ▸ hle
      by_cases hEq : W = VPlus
      · exact Or.inl hEq
      · right; right
        have hnotle : ¬ W ≤ VPlus := fun hle' => hEq (le_antisymm hle' hVPW)
        rw [SetLike.le_def] at hnotle
        push_neg at hnotle
        obtain ⟨v, hvW, hvP⟩ := hnotle
        have hv0 : v ≠ 0 := by intro h0; exact hvP (by rw [h0]; exact Submodule.zero_mem _)
        obtain ⟨m, hm, rfl⟩ := exists_vec v
        have hm0 : m ≠ 0 := by intro h0; exact hv0 (by rw [h0, vec_zero])
        have htri' := orbit_span_trichotomy hK0 h8 hm hm0
        have hle' := orbit_span_le_of_invariant hK0 hW (n := m) hvW
        have hvm : Code.vec m ∈ spanOfList ((pglData ()).elems0.map fun k => Code.act k m).toList :=
          vec_mem_orbit_span hK0 hm
        rcases htri' with hVP' | hVS' | hTop'
        · exact absurd (hVP' ▸ hvm) hvP
        · have hVSW : VStar ≤ W := hVS' ▸ hle'
          have : (⊤ : Submodule (ZMod 2) V₀) ≤ W := by
            rw [← VPlus_sup_VStar h5]
            exact sup_le hVPW hVSW
          exact top_le_iff.mp this
        · have : (⊤ : Submodule (ZMod 2) V₀) ≤ W := hTop' ▸ hle'
          exact top_le_iff.mp this
    · have hVSW : VStar ≤ W := hVS ▸ hle
      by_cases hEq : W = VStar
      · exact Or.inr (Or.inl hEq)
      · right; right
        have hnotle : ¬ W ≤ VStar := fun hle' => hEq (le_antisymm hle' hVSW)
        rw [SetLike.le_def] at hnotle
        push_neg at hnotle
        obtain ⟨v, hvW, hvS⟩ := hnotle
        have hv0 : v ≠ 0 := by intro h0; exact hvS (by rw [h0]; exact Submodule.zero_mem _)
        obtain ⟨m, hm, rfl⟩ := exists_vec v
        have hm0 : m ≠ 0 := by intro h0; exact hv0 (by rw [h0, vec_zero])
        have htri' := orbit_span_trichotomy hK0 h8 hm hm0
        have hle' := orbit_span_le_of_invariant hK0 hW (n := m) hvW
        have hvm : Code.vec m ∈ spanOfList ((pglData ()).elems0.map fun k => Code.act k m).toList :=
          vec_mem_orbit_span hK0 hm
        rcases htri' with hVP' | hVS' | hTop'
        · have hVPW' : VPlus ≤ W := hVP' ▸ hle'
          have : (⊤ : Submodule (ZMod 2) V₀) ≤ W := by
            rw [← VPlus_sup_VStar h5]
            exact sup_le hVPW' hVSW
          exact top_le_iff.mp this
        · exact absurd (hVS' ▸ hvm) hvS
        · have : (⊤ : Submodule (ZMod 2) V₀) ≤ W := hTop' ▸ hle'
          exact top_le_iff.mp this
    · have : (⊤ : Submodule (ZMod 2) V₀) ≤ W := hTop ▸ hle
      exact Or.inr (Or.inr (top_le_iff.mp this))

theorem natCard_KPGL_check {D : PGLData} (hK : EnumCert kPGLGens D.elems.toList)
    (h3 : pglF3Of D = true) : Nat.card KPGL = 336 := by
  have h := hK.natCard
  have hsize := (pglF3Of_facts h3).1
  simpa [KPGL, Array.length_toList, hsize] using h

theorem natCard_KPGL0_check {D : PGLData} (hK0 : EnumCert kPGL0Gens D.elems0.toList)
    (h3 : pglF3Of D = true) : Nat.card KPGL0 = 168 := by
  have h := hK0.natCard
  have hsize := (pglF3Of_facts h3).2
  simpa [KPGL0, Array.length_toList, hsize] using h

theorem pglF4_sound_of (hK : EnumCert kPGLGens (pglData ()).elems.toList)
    (hK0 : EnumCert kPGL0Gens (pglData ()).elems0.toList) (h : pglFactsCheck () = true) :
    ⁅KPGL, KPGL⁆ = KPGL0 := by
  obtain ⟨h1, -, h3, h4, -, -, -, -, -, -, -, -, -⟩ := pglFactsCheck_all h
  obtain ⟨⟨-, -⟩, hinv, -⟩ := pglF1Of_facts h1
  haveI : Finite (V₀ ≃ₗ[ZMod 2] V₀) := finite_linearEquiv
  have hK0K : KPGL0 ≤ KPGL := KPGL0_le_KPGL_of_check hK hK0 h
  have hcardK : Nat.card KPGL = 336 := natCard_KPGL_check hK h3
  have hcardK0 : Nat.card KPGL0 = 168 := natCard_KPGL0_check hK0 h3
  have hle1 : ⁅KPGL, KPGL⁆ ≤ KPGL0 := by
    have hcard_sub : Nat.card ↥(KPGL0.subgroupOf KPGL) = 168 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0K).toEquiv]
      exact hcardK0
    have hidx : (KPGL0.subgroupOf KPGL).index = 2 := by
      rw [Subgroup.index_eq_card_div, hcard_sub, hcardK]
    have hNormal : (KPGL0.subgroupOf KPGL).Normal := Subgroup.normal_of_index_eq_two hidx
    have hcardQ : Nat.card (KPGL ⧸ (KPGL0.subgroupOf KPGL)) = 2 := by
      rw [← Subgroup.index_eq_card, hidx]
    have hcommQ : IsMulCommutative (KPGL ⧸ (KPGL0.subgroupOf KPGL)) := by
      refine ⟨⟨fun x y => ?_⟩⟩
      have hx2 : x * x = 1 := by
        have h := pow_card_eq_one' (x := x)
        rw [hcardQ] at h
        simpa [pow_two] using h
      have hy2 : y * y = 1 := by
        have h := pow_card_eq_one' (x := y)
        rw [hcardQ] at h
        simpa [pow_two] using h
      have hx : x⁻¹ = x := (eq_inv_of_mul_eq_one_right hx2).symm
      have hy : y⁻¹ = y := (eq_inv_of_mul_eq_one_right hy2).symm
      calc x * y = (x * y)⁻¹ := by
            symm
            exact (eq_inv_of_mul_eq_one_right (by
              have h := pow_card_eq_one' (x := x * y)
              rw [hcardQ] at h
              simpa [pow_two] using h)).symm
        _ = y⁻¹ * x⁻¹ := mul_inv_rev _ _
        _ = y * x := by rw [hx, hy]
    have hcommK : _root_.commutator ↥KPGL ≤ KPGL0.subgroupOf KPGL :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hcommQ
    have hmap := Subgroup.map_mono (f := KPGL.subtype) hcommK
    rwa [Subgroup.map_subtype_commutator, Subgroup.subgroupOf_map_subtype,
      inf_of_le_left hK0K] at hmap
  have hle2 : KPGL0 ≤ ⁅KPGL, KPGL⁆ := by
    rw [KPGL0, codeSubgroup, Subgroup.closure_le]
    rintro g ⟨m, hm, hgm⟩
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hm
    obtain ⟨i, x, hi, hx, hcode⟩ := (pglF4Of_facts h4).2.2.2.2 j hj
    have hi_mem : (pglData ()).elems[i]! ∈ (pglData ()).elems.toList := by
      rw [array_getElem!_eq_getElem_of_lt hi]
      exact Array.getElem_mem_toList hi
    have hx_mem : (pglData ()).elems[x]! ∈ (pglData ()).elems.toList := by
      rw [array_getElem!_eq_getElem_of_lt hx]
      exact Array.getElem_mem_toList hx
    let A : V₀ ≃ₗ[ZMod 2] V₀ := hK.elem ((pglData ()).elems[i]!)
    let B : V₀ ≃ₗ[ZMod 2] V₀ := hK.elem ((pglData ()).elems[x]!)
    have hAmem : A ∈ KPGL := hK.elem_mem hi_mem
    have hBmem : B ∈ KPGL := hK.elem_mem hx_mem
    have hAcode : Code.HasCode (A : V₀ →ₗ[ZMod 2] V₀) ((pglData ()).elems[i]!) :=
      hK.hasCode_elem hi_mem
    have hBcode : Code.HasCode (B : V₀ →ₗ[ZMod 2] V₀) ((pglData ()).elems[x]!) :=
      hK.hasCode_elem hx_mem
    have hexA : ∃ H : V₀ ≃ₗ[ZMod 2] V₀,
        Code.HasCode (H : V₀ →ₗ[ZMod 2] V₀) ((pglData ()).invs[i]!) :=
      exists_equiv_of_mul_eq_one (EnumCert.code_mul_comm_one (hinv i hi))
    let HA : V₀ ≃ₗ[ZMod 2] V₀ := Classical.choose hexA
    have hHAcode : Code.HasCode (HA : V₀ →ₗ[ZMod 2] V₀) ((pglData ()).invs[i]!) :=
      Classical.choose_spec hexA
    have hAHA : A * HA = 1 := by
      apply Code.HasCode.eq_of_equiv (hAcode.mul hHAcode)
      rw [hinv i hi]
      exact Code.hasCode_one
    have hHA : HA = A⁻¹ := eq_inv_of_mul_eq_one_right hAHA
    have hexB : ∃ H : V₀ ≃ₗ[ZMod 2] V₀,
        Code.HasCode (H : V₀ →ₗ[ZMod 2] V₀) ((pglData ()).invs[x]!) :=
      exists_equiv_of_mul_eq_one (EnumCert.code_mul_comm_one (hinv x hx))
    let HB : V₀ ≃ₗ[ZMod 2] V₀ := Classical.choose hexB
    have hHBcode : Code.HasCode (HB : V₀ →ₗ[ZMod 2] V₀) ((pglData ()).invs[x]!) :=
      Classical.choose_spec hexB
    have hBHB : B * HB = 1 := by
      apply Code.HasCode.eq_of_equiv (hBcode.mul hHBcode)
      rw [hinv x hx]
      exact Code.hasCode_one
    have hHB : HB = B⁻¹ := eq_inv_of_mul_eq_one_right hBHB
    have hcommcode : Code.HasCode
        (((A * B) * HA * HB : V₀ ≃ₗ[ZMod 2] V₀) : V₀ →ₗ[ZMod 2] V₀)
        (Code.mul (Code.mul (Code.mul ((pglData ()).elems[i]!) ((pglData ()).elems[x]!))
          ((pglData ()).invs[i]!)) ((pglData ()).invs[x]!)) :=
      (((hAcode.mul hBcode).mul hHAcode).mul hHBcode)
    have hgcode : Code.HasCode (g : V₀ →ₗ[ZMod 2] V₀) (kPGL0Gens[j]!) := by
      rw [getElem!_eq_getElem_of_lt hj]
      exact hgm
    rw [hcode] at hcommcode
    have hg_eq : g = (A * B) * HA * HB := hgcode.eq_of_equiv hcommcode
    rw [hg_eq, hHA, hHB]
    exact Subgroup.commutator_mem_commutator hAmem hBmem
  exact le_antisymm hle1 hle2

end CFSG.GF2Type.Smith1979W3.Cert690
