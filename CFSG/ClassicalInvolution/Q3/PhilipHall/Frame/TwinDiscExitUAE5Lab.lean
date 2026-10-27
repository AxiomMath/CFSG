module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitUAE5Trans
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Fam
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscPf9Lie
public import CFSG.ClassicalInvolution.Q3.TL3T32
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEC
public import CFSG.ClassicalInvolution.Q3.TL4VtxE4Red

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.TL4.SecIdE2

namespace TwinDisc

namespace AE5

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}

theorem ker_pGroupN (hS : Q8Section X Φ) (I : AEIdent Φ n) : IsPGroup 2 I.φ.ker := by
  have hgen : pSpan Φ = ⊤ := by
    have := hS.gen
    unfold omegaGen at this
    exact this
  let e : ↥(pSpan Φ) ≃* X := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have hodd : classicalInvolutionOddCore ↥(pSpan Φ) = ⊥ :=
    classicalInvolutionOddCore_eq_bot_of_mulEquiv e.symm hS.oddFree
  exact (Vtx.isPGroup_center_of_oddFree hodd).to_le I.ker_le

theorem members_twoN (hn : 5 ≤ n) (hS : Q8Section X Φ) (I : AEIdent Φ n) : ∀ L ∈ Φ, IsPGroup 2 L := by
  intro L hL x
  obtain ⟨α, h, b, hlab⟩ := I.label L hL
  set y : ↥(pSpan Φ) := ⟨(x : X), le_pSpan hL x.2⟩ with hy
  have hmem : I.φ y ∈ memBar α h b := by
    rw [← hlab]
    exact I.mem_map hL x.2
  have h8 : (⟨I.φ y, hmem⟩ : ↥(memBar α h b)) ^ 8 = 1 := by
    have := pow_card_eq_one' (G := ↥(memBar α h b)) (x := ⟨I.φ y, hmem⟩)
    rwa [natCard_memBar hn] at this
  have hker : y ^ 8 ∈ I.φ.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    simpa using congrArg (fun z : ↥(memBar α h b) => (z : AEQ n)) h8
  obtain ⟨k, hk⟩ := ker_pGroupN hS I ⟨y ^ 8, hker⟩
  refine ⟨k + 3, ?_⟩
  apply Subtype.ext
  have h1 := congrArg (fun z : ↥I.φ.ker => ((z : ↥(pSpan Φ)) : X)) hk
  simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1
  have e : ((x : X)) ^ 2 ^ (k + 3) = (((y ^ 8) ^ 2 ^ k : ↥(pSpan Φ)) : X) := by
    simp only [Subgroup.coe_pow, hy]
    rw [← pow_mul]
    congr 1
    rw [pow_add]
    ring
  simpa [e] using h1

theorem q8FamN_of_trans (hn : 5 ≤ n) (hS : Q8Section X Φ)
    (htrans : ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L) (I : AEIdent Φ n) :
    ExitO2.Q8Fam X Φ := by
  have h2 := members_twoN hn hS I
  have hgen : pSpan Φ = ⊤ := by
    have := hS.gen
    unfold omegaGen at this
    exact this
  refine ⟨hS.hyp, h2, fun J hJ => ?_, hS.aEmpty, hgen, htrans, hS.oddFree, ?_⟩
  · have hKS : IsSylow2In J J := ⟨le_rfl, h2 J hJ, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
    exact hS.q8 _ hJ _ hKS
  · intro L hL u hu
    set ψ : ↥(pSpan Φ) →* Equiv.Perm (Fin n) := (permQ n).comp I.φ with hψ
    have hker2 : IsPGroup 2 ψ.ker := by
      intro g
      have hg : I.φ g.1 * I.φ g.1 = 1 := by
        have h3 : permQ n (I.φ g.1) = 1 := MonoidHom.mem_ker.mp g.2
        exact mul_self_of_mem_ker_permQ (MonoidHom.mem_ker.mpr h3)
      have hsq : (g.1 * g.1) ∈ I.φ.ker := by
        rw [MonoidHom.mem_ker, map_mul]; exact hg
      obtain ⟨k, hk⟩ := ker_pGroupN hS I ⟨g.1 * g.1, hsq⟩
      refine ⟨k + 1, ?_⟩
      apply Subtype.ext
      have h1 := congrArg (fun z : ↥I.φ.ker => ((z : ↥(pSpan Φ))) ) hk
      simp only [Subgroup.coe_pow, OneMemClass.coe_one] at h1
      show (g.1 ^ 2 ^ (k + 1)) = 1
      rw [pow_succ, pow_mul', pow_two]
      exact h1
    refine ⟨ψ.ker.map (pSpan Φ).subtype, ?_, ?_, ?_⟩
    · refine Subgroup.Normal.map inferInstance _ ?_
      intro y
      exact ⟨⟨y, by rw [hgen]; trivial⟩, rfl⟩
    · exact hker2.map _
    · obtain ⟨α, h, b, hlab⟩ := I.label L hL
      have hmem : I.φ ⟨u, le_pSpan hL hu.mem⟩ ∈ memBar α h b := by
        rw [← hlab]; exact I.mem_map hL hu.mem
      have hsq : I.φ ⟨u, le_pSpan hL hu.mem⟩ * I.φ ⟨u, le_pSpan hL hu.mem⟩ = 1 := by
        rw [← map_mul]
        have : (⟨u, le_pSpan hL hu.mem⟩ * ⟨u, le_pSpan hL hu.mem⟩ : ↥(pSpan Φ)) = 1 :=
          Subtype.ext hu.sq
        rw [this, map_one]
      refine ⟨⟨u, le_pSpan hL hu.mem⟩, ?_, rfl⟩
      refine MonoidHom.mem_ker.mpr ?_
      show permQ n (I.φ _) = 1
      rcases eq_of_mem_memBar_mul_self hn hmem hsq with h1 | h1
      · rw [h1, map_one]
      · rw [h1]
        exact zOf_perm _


section Trans

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)} {n : ℕ}

theorem members_card8 (hn : 5 ≤ n) (hS : Q8Section X Φ) (I : AEIdent Φ n) :
    ∀ L ∈ Φ, Nat.card ↥L = 8 := by
  intro L hL
  have h2 := members_twoN hn hS I L hL
  have hKS : IsSylow2In L L := ⟨le_rfl, h2, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨e⟩ := hS.q8 _ hL _ hKS
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]

theorem members_exists_sq (hn : 5 ≤ n) (hS : Q8Section X Φ) (I : AEIdent Φ n) :
    ∀ L ∈ Φ, ∃ x ∈ L, x * x ≠ 1 := by
  intro L hL
  have h2 := members_twoN hn hS I L hL
  have hKS : IsSylow2In L L := ⟨le_rfl, h2, fun V' hV'K _ hKV' => le_antisymm hV'K hKV'⟩
  obtain ⟨e⟩ := hS.q8 _ hL _ hKS
  refine ⟨((e.symm (QuaternionGroup.a 1) : ↥L) : X), (e.symm (QuaternionGroup.a 1)).2, fun h => ?_⟩
  have h' : e.symm (QuaternionGroup.a 1 * QuaternionGroup.a 1) = 1 := by
    rw [map_mul]
    exact Subtype.ext h
  rw [MulEquiv.map_eq_one_iff] at h'
  exact absurd h' (by decide)

theorem hgen_of (hS : Q8Section X Φ) : pSpan Φ = ⊤ := by
  have := hS.gen
  unfold omegaGen at this
  exact this

theorem eq_of_phi_mem_n (hn : 5 ≤ n) (hS : Q8Section X Φ) (I : AEIdent Φ n)
    {K J : Subgroup X} (hK : K ∈ Φ) (hJ : J ∈ Φ) {a : X} (haK : a ∈ K) (ha2 : a * a ≠ 1)
    (haJ : I.φ ⟨a, le_pSpan hK haK⟩ ∈ (J.subgroupOf (pSpan Φ)).map I.φ) : K = J := by
  have htop : pSpan Φ = ⊤ := hgen_of hS
  have hZc : I.φ.ker.map (pSpan Φ).subtype ≤ Subgroup.center X := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : y ∈ pSpan Φ := htop ▸ Subgroup.mem_top y
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (I.ker_le hk) ⟨y, hy⟩)
  have hZK : ∀ L ∈ Φ, I.φ.ker.map (pSpan Φ).subtype ⊓ L = ⊥ := by
    intro L hL
    rw [eq_bot_iff]
    rintro x ⟨⟨k, hk, hkx⟩, hxL⟩
    obtain ⟨α, h, b, hlab⟩ := I.label L hL
    have h8 : Nat.card ↥L = 8 := members_card8 hn hS I L hL
    rw [Subgroup.mem_bot]
    refine phi_injOn I.φ hn hL h8 hlab hxL L.one_mem ?_
    have hk1 : I.φ k = 1 := hk
    have hk' : k = ⟨x, le_pSpan hL hxL⟩ := Subtype.ext hkx
    rw [← hk', hk1]
    exact (map_one I.φ).symm
  obtain ⟨⟨j, hjP⟩, hjJ, hja⟩ := haJ
  have hjJ' : j ∈ J := Subgroup.mem_subgroupOf.mp hjJ
  have hcZ : j⁻¹ * a ∈ I.φ.ker.map (pSpan Φ).subtype := by
    refine ⟨⟨j, hjP⟩⁻¹ * ⟨a, le_pSpan hK haK⟩, ?_, rfl⟩
    show I.φ (⟨j, hjP⟩⁻¹ * ⟨a, le_pSpan hK haK⟩) = 1
    rw [map_mul, map_inv, hja, inv_mul_cancel]
  exact eq_of_mem_sup_center hS.hyp (members_twoN hn hS I) hZc hZK hK hJ haK ha2 hjJ' hcZ (by group)

theorem same_of_image_n (hn : 5 ≤ n) (hS : Q8Section X Φ) (I : AEIdent Φ n) {L M : Subgroup X}
    (hL : L ∈ Φ) (hM : M ∈ Φ)
    (hLM : (L.subgroupOf (pSpan Φ)).map I.φ = (M.subgroupOf (pSpan Φ)).map I.φ) : L = M := by
  obtain ⟨a, haL, ha2⟩ := members_exists_sq hn hS I L hL
  refine eq_of_phi_mem_n hn hS I hL hM haL ha2 ?_
  rw [← hLM]
  exact I.mem_map hL haL

theorem label_conj (I : AEIdent Φ n) {L : Subgroup X} (hL : L ∈ Φ) (y : ↥(pSpan Φ)) :
    ((conjSub (y : X) L).subgroupOf (pSpan Φ)).map I.φ =
      ((L.subgroupOf (pSpan Φ)).map I.φ).map (MulAut.conj (I.φ y)).toMonoidHom := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : (z : X) ∈ conjSub (y : X) L := hz
    obtain ⟨l, hl, hlz⟩ := Subgroup.mem_map.mp hz'
    set l' : ↥(pSpan Φ) := ⟨l, le_pSpan hL hl⟩ with hl'
    have hzz : z = y * l' * y⁻¹ := by
      apply Subtype.ext
      rw [← hlz]
      rfl
    refine Subgroup.mem_map.mpr ⟨I.φ l', I.mem_map hL hl, ?_⟩
    rw [hzz]
    simp [MulAut.conj_apply]
  · rintro ⟨m, ⟨l', hl', rfl⟩, rfl⟩
    have hl'' : (l' : X) ∈ L := Subgroup.mem_subgroupOf.mp hl'
    refine ⟨y * l' * y⁻¹, ?_, ?_⟩
    · apply Subgroup.mem_subgroupOf.mpr
      refine Subgroup.mem_map.mpr ⟨(l' : X), hl'', ?_⟩
      simp [MulAut.conj_apply]
    · simp [MulAut.conj_apply]

theorem trans_of_aeIdent (hn : 5 ≤ n) (hS : Q8Section X Φ) (I : AEIdent Φ n) :
    ∀ K ∈ Φ, ∀ L ∈ Φ, ∃ g : X, conjSub g K = L := by
  intro K hK L hL
  obtain ⟨α, h, b, hlab⟩ := I.label K hK
  obtain ⟨β, h', c, hlab'⟩ := I.label L hL
  obtain ⟨w, hw, hconj⟩ := exists_conj_label hn h h' b c
  have hmem : mkQ n w ∈ I.φ.range := by
    rw [I.range_eq]
    exact ⟨w, hw, rfl⟩
  obtain ⟨y, hy⟩ := hmem
  refine ⟨(y : X), same_of_image_n hn hS I (hS.hyp.conjInvariant (y : X) K hK) hL ?_⟩
  rw [label_conj I hK y, hlab, hlab', hy, ← hconj]

theorem q8Fam_of_aeIdent_n (hn : 5 ≤ n) (hS : Q8Section X Φ) (I : AEIdent Φ n) :
    ExitO2.Q8Fam X Φ :=
  q8FamN_of_trans hn hS (trans_of_aeIdent hn hS I) I

end Trans

end AE5

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
