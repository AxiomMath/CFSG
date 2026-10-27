module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Th.LocalDataTh.Sylow

public section

namespace CFSG.EvenSporadicStandard.ThStd.LocalDataTh

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Max3
open scoped Matrix commutatorElement

section Facts


theorem Pt_eq_one_of_forall {T : Mat8} (hT : T ∈ Pt) (h : ∀ v : Vec, (T + 1) *ᵥ v ∈ Ksem 2) :
    T = 1 := by
  obtain ⟨a, ha, rfl⟩ := mem_Pt_iff.1 hT
  by_cases hid : a = idCols 8
  · rw [hid, matOfCols_idCols]
  · exfalso
    obtain ⟨c₀, hc₀, hnot⟩ := ptFacts.2.2.2.2.2.2.1 a ha hid
    have h1 := h (codeVec 8 c₀)
    rw [add_one_mulVec_codeVec] at h1
    obtain ⟨d, hd, hdeq⟩ := h1
    have hlt : applyCols 8 a c₀ ^^^ c₀ < 256 :=
      Nat.xor_lt_two_pow (n := 8) (applyCols_lt (Pc_wf a ha) c₀) hc₀
    exact hnot (by rwa [← codeVec_inj_of_lt (Kc_lt 2 d hd) hlt hdeq])

theorem Ksem3_iff {v : Vec} : v ∈ Ksem 3 ↔ ∃ c ∈ UCodes, codeVec 8 c = v := by
  obtain ⟨-, -, -, -, -, hK3, -⟩ := ptFacts
  constructor
  · rintro ⟨c, hc, rfl⟩
    exact ⟨c, (hK3 c (Kc_lt 3 c hc)).1 hc, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    have hlt : c < 256 := by
      have : ∀ c ∈ UCodes, c < 256 := by decide
      exact this c hc
    exact ⟨c, (hK3 c hlt).2 hc, rfl⟩

theorem zero_mem_Ksem3 : (0 : Vec) ∈ Ksem 3 :=
  Ksem3_iff.2 ⟨0, by simp [UCodes], codeVec_zero 8⟩

theorem Ksem3_add {u w : Vec} (hu : u ∈ Ksem 3) (hw : w ∈ Ksem 3) : u + w ∈ Ksem 3 := by
  obtain ⟨cu, hcu, rfl⟩ := Ksem3_iff.1 hu
  obtain ⟨cw, hcw, rfl⟩ := Ksem3_iff.1 hw
  exact Ksem3_iff.2 ⟨cu ^^^ cw, ptFacts.2.2.2.2.2.2.2.1 cu hcu cw hcw, codeVec_xor 8 cu cw⟩

theorem qf_Ksem3 {u : Vec} (hu : u ∈ Ksem 3) : CFSG.Certificates.ExtraspecialNF.qf c u = 0 := by
  obtain ⟨cu, hcu, rfl⟩ := Ksem3_iff.1 hu
  exact ptFacts.2.2.2.2.2.2.2.2.1 cu hcu

theorem bil_Ksem3 {u w : Vec} (hu : u ∈ Ksem 3) (hw : w ∈ Ksem 3) :
    CFSG.Certificates.ExtraspecialNF.bil c u w = 0 := by
  obtain ⟨cu, hcu, rfl⟩ := Ksem3_iff.1 hu
  obtain ⟨cw, hcw, rfl⟩ := Ksem3_iff.1 hw
  exact ptFacts.2.2.2.2.2.2.2.2.2.1 cu hcu cw hcw

theorem card_Ksem3 : Nat.card ↥(Ksem 3) = 8 := by
  have e : Ksem 3 = ↑((UCodes.map (codeVec 8)).toFinset) := by
    ext v
    simp [Ksem3_iff]
  rw [e, Nat.card_coe_set_eq, Set.ncard_coe_finset]
  decide

end Facts

section Group


@[expose] noncomputable def A : Subgroup J where
  carrier := {g | ∃ (s : ZMod 2) (u : Vec), u ∈ Ksem 3 ∧ nf s u = g}
  one_mem' := ⟨0, 0, zero_mem_Ksem3, nf_zero_zero⟩
  mul_mem' := by
    rintro _ _ ⟨s, u, hu, rfl⟩ ⟨t, w, hw, rfl⟩
    exact ⟨_, u + w, Ksem3_add hu hw, (nf_mul s t u w).symm⟩
  inv_mem' := by
    rintro _ ⟨s, u, hu, rfl⟩
    exact ⟨_, u, hu, (inv_nf s u).symm⟩

theorem mem_A_iff' {x : J} : x ∈ A ↔ ∃ (s : ZMod 2) (u : Vec), u ∈ Ksem 3 ∧ nf s u = x := Iff.rfl

theorem z_mem_A : z ∈ A :=
  ⟨1, 0, zero_mem_Ksem3, CFSG.Certificates.ExtraspecialNF.nf_one_zero z q⟩

theorem A_comm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := by
  rintro _ ⟨s, u, hu, rfl⟩ _ ⟨t, w, hw, rfl⟩
  have h := CFSG.Certificates.ExtraspecialNF.nf_mul_comm symplectic_rel (fun i j => c_symm j i)
    (by decide) s t u w
  rw [bil_Ksem3 hu hw, ZMod.val_zero, pow_zero, mul_one] at h
  exact h

theorem A_sq : ∀ x ∈ A, x ^ 2 = 1 := by
  rintro _ ⟨s, u, hu, rfl⟩
  rw [nf_sq, qf_Ksem3 hu, ZMod.val_zero, pow_zero]

theorem A_card : Nat.card A = 16 := by
  have hbij : Function.Bijective fun p : ZMod 2 × ↥(Ksem 3) =>
      (⟨nf p.1 p.2, ⟨p.1, p.2, p.2.2, rfl⟩⟩ : A) := by
    constructor
    · intro p p' h
      have h1 := congrArg Subtype.val h
      have h2 := nf_injective (a₁ := (p.1, (p.2 : Vec))) (a₂ := (p'.1, (p'.2 : Vec))) h1
      exact Prod.ext (Prod.mk.inj h2).1 (Subtype.ext (Prod.mk.inj h2).2)
    · rintro ⟨_, s, u, hu, rfl⟩
      exact ⟨(s, ⟨u, hu⟩), rfl⟩
  rw [← Nat.card_eq_of_bijective _ hbij, Nat.card_prod, card_Ksem3, Nat.card_zmod]

theorem commutator_nf_zero {σ : J} (hσ : σ ∈ M) (s : ZMod 2) : ⁅nf s 0, σ⁆ = 1 := by
  rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases s with rfl | rfl
  · rw [nf_zero_zero]
    simp
  · have h1 : (nf 1 0 : J) = z := CFSG.Certificates.ExtraspecialNF.nf_one_zero z q
    rw [h1]
    exact commutatorElement_eq_one_iff_mul_comm.2 (commute_z_of_mem_M hσ).eq

end Group

section Ladder


@[expose] noncomputable def Phi : ℕ → J → Prop
  | 0, y => y = 1
  | k + 1, y => ∀ s ∈ S, Phi k ⁅y, s⁆

theorem phi_one_nf (s : ZMod 2) (v : Vec) : Phi 1 (nf s v) ↔ v ∈ Ksem 0 := by
  rw [Ksem_zero]
  show (∀ σ ∈ S, ⁅nf s v, σ⁆ = 1) ↔ v = 0
  constructor
  · intro h
    have hc : ∀ y ∈ S, nf s v * y = y * nf s v := by
      intro y hy
      have h1 : ⁅nf s v, y⁆ = 1 := h y hy
      rw [commutatorElement_def] at h1
      calc nf s v * y = (nf s v * y * (nf s v)⁻¹ * y⁻¹) * y * nf s v := by group
        _ = y * nf s v := by rw [h1, one_mul]
    obtain ⟨b, hb⟩ := (CFSG.Certificates.ExtraspecialNF.mem_zpowers_iff_exists
      symplectic_rel).1 (center_le_S _ (nf_mem_S s v) hc)
    have hb' : nf b 0 = nf s v := by rw [nf_zero_vec]; exact hb
    exact (congrArg Prod.snd (nf_injective (a₁ := (b, 0)) (a₂ := (s, v)) hb')).symm
  · rintro rfl σ hσ
    exact commutator_nf_zero hσ.1 s

theorem phi_nf_iff : ∀ (k : ℕ) (s : ZMod 2) (v : Vec), Phi (k + 1) (nf s v) ↔ v ∈ Ksem k
  | 0, s, v => phi_one_nf s v
  | k + 1, s, v => by
    show (∀ σ ∈ S, Phi (k + 1) ⁅nf s v, σ⁆) ↔ v ∈ Ksem (k + 1)
    rw [← Ksem_step Pc_wf k v]
    constructor
    · intro h T hT
      obtain ⟨σ, hσ, rfl⟩ := mem_Pt_iff_exists_S.1 hT
      obtain ⟨t, ht⟩ := comm_nf' hσ.1 s v
      have h1 := h σ hσ
      rwa [ht, phi_nf_iff k t] at h1
    · intro h σ hσ
      obtain ⟨t, ht⟩ := comm_nf' hσ.1 s v
      rw [ht, phi_nf_iff k t]
      exact h _ hσ.2

theorem mem_Q_of_phi_four {x : J} (hx : x ∈ S) (h : Phi 4 x) : x ∈ Q := by
  have hρ : rho x = 1 := by
    refine Pt_eq_one_of_forall hx.2 fun v => ?_
    have h3 : Phi 3 ⁅x, nf 0 v⁆ := h _ (nf_mem_S 0 v)
    obtain ⟨t, ht⟩ := comm_nf hx.1 0 v
    rw [ht, phi_nf_iff 2] at h3
    exact h3
  exact (rho_eq_one_iff hx.1).1 hρ

theorem mem_A_iff (x : J) : x ∈ A ↔ x ∈ S ∧ ∀ s₁ ∈ S, ∀ s₂ ∈ S, ∀ s₃ ∈ S, ∀ s₄ ∈ S,
    ⁅⁅⁅⁅x, s₁⁆, s₂⁆, s₃⁆, s₄⁆ = 1 := by
  constructor
  · rintro ⟨s, u, hu, rfl⟩
    exact ⟨nf_mem_S s u, (phi_nf_iff 3 s u).2 hu⟩
  · rintro ⟨hxS, hx⟩
    have h4 : Phi 4 x := hx
    obtain ⟨s, v, rfl⟩ := mem_Q_iff.1 (mem_Q_of_phi_four hxS h4)
    exact ⟨s, v, (phi_nf_iff 3 s v).1 h4, rfl⟩

end Ladder

end CFSG.EvenSporadicStandard.ThStd.LocalDataTh
