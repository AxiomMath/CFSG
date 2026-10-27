module

public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinDiscExitO2Fam
public import CFSG.ClassicalInvolution.Q3.TL3T23
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEC
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEM
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TL4 CFSG.ClassicalInvolution.Q3.TL4.SecIdE2

namespace TwinDisc

namespace ExitO2

variable {Y : Type} [Group Y] [Finite Y] {Δ : Set (Subgroup Y)}

section Phi

variable {m : ℕ} (φ : ↥(pSpan (Δ)) →* AE.AEQ m)

theorem fam_eq_of_phi_mem (F : Q8Fam Y Δ)
    (hm : 5 ≤ m) (hker : φ.ker ≤ Subgroup.center ↥(pSpan (Δ)))
    (hlabel : ∀ L ∈ Δ, ∃ (α : Finset (Fin m))
      (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (Δ))).map φ = AE.memBar α h b)
    {K J : Subgroup Y} (hK : K ∈ Δ)
    (hJ : J ∈ Δ) {a : Y} (haK : a ∈ K) (ha2 : a * a ≠ 1)
    (haJ : φ ⟨a, le_pSpan hK haK⟩ ∈
      (J.subgroupOf (pSpan (Δ))).map φ) : K = J := by
  have htop : pSpan (Δ) = ⊤ := F.gen
  have hZc : φ.ker.map (pSpan (Δ)).subtype ≤
      Subgroup.center Y := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : y ∈ pSpan (Δ) := htop ▸ Subgroup.mem_top y
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hker hk) ⟨y, hy⟩)
  have hZK : ∀ L ∈ Δ,
      φ.ker.map (pSpan (Δ)).subtype ⊓ L = ⊥ := by
    intro L hL
    rw [eq_bot_iff]
    rintro x ⟨⟨k, hk, hkx⟩, hxL⟩
    obtain ⟨α, h, b, hlab⟩ := hlabel L hL
    have h8 : Nat.card ↥L = 8 := (F.card L hL).trans (by norm_num)
    rw [Subgroup.mem_bot]
    refine phi_injOn φ hm hL h8 hlab hxL L.one_mem ?_
    have hk1 : φ k = 1 := hk
    have hk' : k = ⟨x, le_pSpan hL hxL⟩ := Subtype.ext hkx
    rw [← hk', hk1]
    exact (map_one φ).symm
  obtain ⟨⟨j, hjP⟩, hjJ, hja⟩ := haJ
  have hjJ' : j ∈ J := Subgroup.mem_subgroupOf.mp hjJ
  have hcZ : j⁻¹ * a ∈ φ.ker.map (pSpan (Δ)).subtype := by
    refine ⟨⟨j, hjP⟩⁻¹ * ⟨a, le_pSpan hK haK⟩, ?_, rfl⟩
    show φ (⟨j, hjP⟩⁻¹ * ⟨a, le_pSpan hK haK⟩) = 1
    rw [map_mul, map_inv, hja, inv_mul_cancel]
  exact eq_of_mem_sup_center F.hyp (F.two) hZc hZK hK hJ haK ha2 hjJ'
    hcZ (by group)

theorem fam_mem_omegaStarNbr_of_phi (F : Q8Fam Y Δ) (hm : 5 ≤ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (Δ)))
    (hlabel : ∀ L ∈ Δ, ∃ (α : Finset (Fin m))
      (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (Δ))).map φ = AE.memBar α h b)
    {L L' : Subgroup Y} (hL : L ∈ Δ)
    (hL' : L' ∈ Δ) (hne : L ≠ L')
    {α β : Finset (Fin m)} {h : α.card = 4} {h' : β.card = 4} {b c : Bool}
    (hlab : (L.subgroupOf (pSpan (Δ))).map φ =
      AE.memBar α h b)
    (hlab' : (L'.subgroupOf (pSpan (Δ))).map φ =
      AE.memBar β h' c)
    (hv : ∃ v ∈ AE.memBar β h' c, v * v ≠ 1 ∧
      ∀ a ∈ AE.memBar α h b, v * a * v⁻¹ ∈ AE.memBar α h b) :
    L' ∈ omegaStarNbr (Δ) L := by
  obtain ⟨v, hv, hvv, hvn⟩ := hv
  rw [← hlab'] at hv
  obtain ⟨⟨x, hxP⟩, hxL', rfl⟩ := hv
  have hxL : x ∈ L' := Subgroup.mem_subgroupOf.mp hxL'
  have hxx : x * x ≠ 1 := fun h1 => hvv (by
    rw [← map_mul, ← map_one φ]
    exact congrArg φ (Subtype.ext h1))
  have hx4 : orderOf x = 4 := by
    have := orderOf_eq_prime_pow (x := x) (p := 2) (n := 1) (by rw [pow_one, pow_two]; exact hxx)
      (by rw [show 2 ^ (1 + 1) = 4 by norm_num]; exact F.pow_four L' hL' x hxL)
    simpa using this
  obtain ⟨l, hlL, hll⟩ := F.exists_mul_self_ne_one L hL
  have hconjL : conjSub x L ∈ Δ :=
    F.hyp.conjInvariant x L hL
  have hxlx : x * l * x⁻¹ ∈ conjSub x L := conj_mem_conjSub hlL
  have hconj : conjSub x L = L := by
    refine fam_eq_of_phi_mem φ F hm hker hlabel hconjL hL hxlx ?_ ?_
    · intro h1
      apply hll
      calc l * l = x⁻¹ * ((x * l * x⁻¹) * (x * l * x⁻¹)) * x := by group
        _ = 1 := by rw [h1]; group
    · rw [hlab]
      have hl : φ ⟨l, le_pSpan hL hlL⟩ ∈ AE.memBar α h b := by
        rw [← hlab]
        exact ⟨⟨l, le_pSpan hL hlL⟩, Subgroup.mem_subgroupOf.mpr hlL, rfl⟩
      have h2 := hvn _ hl
      have h3 : (⟨x * l * x⁻¹, le_pSpan hconjL hxlx⟩ :
          ↥(pSpan (Δ))) =
          ⟨x, hxP⟩ * ⟨l, le_pSpan hL hlL⟩ * (⟨x, hxP⟩)⁻¹ := rfl
      rw [h3, map_mul, map_mul, map_inv]
      exact h2
  have h2L' : IsPGroup 2 ↥L' := F.two L' hL'
  refine ⟨hL', hne.symm, Subgroup.zpowers x, ?_, Subgroup.zpowers_le.mpr hxL,
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hconj)⟩
  exact mem_USet_of_natCard hL' ⟨le_rfl, h2L', fun V hV _ hLV => le_antisymm hV hLV⟩
    (Subgroup.zpowers_le.mpr hxL) inferInstance
    (by rw [F.card L' hL', Nat.card_zpowers, hx4]; norm_num)

theorem fam_dstarConnected_of_phi (F : Q8Fam Y Δ) (hm : 5 ≤ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (Δ)))
    {𝒜 : Set (Finset (Fin m))} (h𝒜 : ∀ α ∈ 𝒜, α.card = 4)
    (hlabel : ∀ L ∈ Δ, ∃ α ∈ 𝒜, ∃ (h : α.card = 4)
      (b : Bool),
      (L.subgroupOf (pSpan (Δ))).map φ = AE.memBar α h b)
    (hsurj : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ Δ,
      (L.subgroupOf (pSpan (Δ))).map φ = AE.memBar α h b)
    (hconn : ∀ α ∈ 𝒜, ∀ β ∈ 𝒜, Relation.ReflTransGen (fun γ δ => δ ∈ 𝒜 ∧ Adj4 γ δ) α β) :
    T3.DStarConnected (Δ) := by
  have hlabel' : ∀ L ∈ Δ, ∃ (α : Finset (Fin m))
      (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (Δ))).map φ = AE.memBar α h b :=
    fun L hL => by
      obtain ⟨α, -, h, b, hlab⟩ := hlabel L hL
      exact ⟨α, h, b, hlab⟩
  have hsame : ∀ L ∈ Δ, ∀ M ∈ Δ,
      (L.subgroupOf (pSpan (Δ))).map φ =
        (M.subgroupOf (pSpan (Δ))).map φ → L = M := by
    intro L hL M hM hLM
    obtain ⟨a, haL, ha2⟩ := F.exists_mul_self_ne_one L hL
    refine fam_eq_of_phi_mem φ F hm hker hlabel' hL hM haL ha2 ?_
    rw [← hLM]
    exact ⟨⟨a, le_pSpan hL haL⟩, Subgroup.mem_subgroupOf.mpr haL, rfl⟩
  have hstep : ∀ L ∈ Δ, ∀ L' ∈ Δ, ∀ {α β : Finset (Fin m)} {h : α.card = 4} {h' : β.card = 4} {b c : Bool},
      (L.subgroupOf (pSpan (Δ))).map φ = AE.memBar α h b →
      (L'.subgroupOf (pSpan (Δ))).map φ =
        AE.memBar β h' c →
      (∃ v ∈ AE.memBar β h' c, v * v ≠ 1 ∧
        ∀ a ∈ AE.memBar α h b, v * a * v⁻¹ ∈ AE.memBar α h b) →
      Relation.ReflTransGen (dstarAdj (Δ)) L L' ∧
        Relation.ReflTransGen (dstarAdj (Δ)) L' L := by
    intro L hL L' hL' α β h h' b c hlab hlab' hv
    by_cases hLL : L = L'
    · subst hLL
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    · have h1 := fam_mem_omegaStarNbr_of_phi φ F hm hker hlabel' hL hL' hLL hlab hlab' hv
      exact ⟨Relation.ReflTransGen.single ⟨hL', Or.inl h1⟩,
        Relation.ReflTransGen.single ⟨hL, Or.inr h1⟩⟩
  have hto : ∀ L ∈ Δ, ∀ M ∈ Δ, ∀ {α : Finset (Fin m)} {h : α.card = 4} {b : Bool},
      (L.subgroupOf (pSpan (Δ))).map φ = AE.memBar α h b →
      (M.subgroupOf (pSpan (Δ))).map φ =
        AE.memBar α h true →
      Relation.ReflTransGen (dstarAdj (Δ)) L M ∧
        Relation.ReflTransGen (dstarAdj (Δ)) M L := by
    intro L hL M hM α h b hlab hlabM
    cases b
    · exact hstep L hL M hM hlab hlabM
        (exists_normalizing_memBar_of_comm hm fun x hx y hy =>
          (comm_memBar_twin α h y hy x hx).symm)
    · have hLM := hsame L hL M hM (hlab.trans hlabM.symm)
      subst hLM
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
  have hpath : ∀ {α β : Finset (Fin m)}, α ∈ 𝒜 →
      Relation.ReflTransGen (fun γ δ => δ ∈ 𝒜 ∧ Adj4 γ δ) α β →
      ∀ L ∈ Δ, ∀ (h : α.card = 4),
      (L.subgroupOf (pSpan (Δ))).map φ =
        AE.memBar α h true →
      β ∈ 𝒜 ∧ ∀ M ∈ Δ, ∀ (h' : β.card = 4),
        (M.subgroupOf (pSpan (Δ))).map φ =
          AE.memBar β h' true →
        Relation.ReflTransGen (dstarAdj (Δ)) L M := by
    intro α β hα hαβ L hL h hlab
    induction hαβ with
    | refl =>
      refine ⟨hα, fun M hM h' hlabM => ?_⟩
      rw [hsame L hL M hM (hlab.trans hlabM.symm)]
    | tail _ hγδ ih =>
      obtain ⟨hγ, hγL⟩ := ih
      obtain ⟨hδ, hadj⟩ := hγδ
      refine ⟨hδ, fun M hM h' hlabM => ?_⟩
      obtain ⟨N, hN, hlabN⟩ := hsurj _ hγ (h𝒜 _ hγ) true
      refine (hγL N hN (h𝒜 _ hγ) hlabN).trans (hstep N hN M hM hlabN hlabM ?_).1
      rcases hadj with h2 | hdisj
      · exact exists_normalizing_memBar hm _ _ h2
      · exact exists_normalizing_memBar_of_comm hm (AE.comm_memBar_of_disjoint hdisj true true)
  intro K hK J hJ
  obtain ⟨α, hα, h, b, hlabK⟩ := hlabel K hK
  obtain ⟨β, hβ, h', c, hlabJ⟩ := hlabel J hJ
  obtain ⟨Kα, hKα, hlabKα⟩ := hsurj α hα h true
  obtain ⟨Jβ, hJβ, hlabJβ⟩ := hsurj β hβ h' true
  exact ((hto K hK Kα hKα hlabK hlabKα).1.trans
    ((hpath hα (hconn α hα β hβ) Kα hKα h hlabKα).2 Jβ hJβ h' hlabJβ)).trans
    (hto J hJ Jβ hJβ hlabJ hlabJβ).2

end Phi

theorem fam_dstarConnected_of_aeIdent (F : Q8Fam Y Δ) {m : ℕ} (hm : 6 ≤ m)
    (I : AEIdent (Δ) m) :
    T3.DStarConnected (Δ) := by
  refine fam_dstarConnected_of_phi I.φ F (by omega) I.ker_le (𝒜 := {α | α.card = 4})
    (fun α hα => hα) (fun L hL => ?_) (fun α _ h b => I.label_surj α h b) (fun α hα β hβ => ?_)
  · obtain ⟨α, h, b, hlab⟩ := I.label L hL
    exact ⟨α, h, h, b, hlab⟩
  · obtain ⟨γ, hγ, h1, h2⟩ := exists_mid hm hα hβ
    have hαγ : Relation.ReflTransGen (fun γ δ : Finset (Fin m) => δ ∈ {α | α.card = 4} ∧
        Adj4 γ δ) α γ := by
      rcases h1 with rfl | h1
      · exact Relation.ReflTransGen.refl
      · exact Relation.ReflTransGen.single ⟨hγ, h1⟩
    rcases h2 with rfl | h2
    · exact hαγ
    · exact hαγ.tail ⟨hβ, h2⟩

theorem fam_dstarConnected_of_e64 (F : Q8Fam Y Δ)
    (I : AEIdentOn (Δ) 7 AE.e64Sets AE.e64Sub) :
    T3.DStarConnected (Δ) := by
  refine fam_dstarConnected_of_phi I.φ F (by norm_num) I.ker_le
    (fun α hα => card_of_mem_e64Sets hα) I.label (fun α hα h b => I.label_surj α hα h b)
    (fun α hα β hβ => ?_)
  by_cases hαβ : α = β
  · subst hαβ
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨hβ, adj4_of_mem_e64Sets hα hβ hαβ⟩

theorem fam_dstarConnected_of_e29 (F : Q8Fam Y Δ)
    (I : AEIdentOn (Δ) 8 AE.e29Sets AE.e29Sub) :
    T3.DStarConnected (Δ) := by
  refine fam_dstarConnected_of_phi I.φ F (by norm_num) I.ker_le
    (fun α hα => card_of_mem_e29Sets hα) I.label (fun α hα h b => I.label_surj α hα h b)
    (fun α hα β hβ => ?_)
  by_cases hαβ : α = β
  · subst hαβ
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨hβ, adj4_of_mem_e29Sets hα hβ hαβ⟩


end ExitO2

end TwinDisc

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame
