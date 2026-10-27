module

public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2A
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEM
public import CFSG.ClassicalInvolution.Q3.TL4SecIdE2AEC
public import CFSG.ClassicalInvolution.Q3.TL3T23

public section

namespace CFSG.ClassicalInvolution.Q3.TL4.SecIdE2

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Asc77.Thompson
open CFSG.ClassicalInvolution.Disconnected.AschTight CFSG.ClassicalInvolution.Q3.TC.Thin
open CFSG.ClassicalInvolution.Q3.TL4.AlphaFr.E2D (isPGroup_mem card_mem pSpan_eq_top)

variable {Y : Type} [Group Y] [Finite Y] {R : Subgroup Y} {S : Sylow 2 R} {t : Y}

theorem pow_four_eq_one (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ x ∈ L, x ^ 4 = 1 := by
  obtain ⟨e⟩ : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) := hc.1
  have hK : ∀ y ∈ tightCore R, y ^ 4 = 1 := by
    intro y hy
    rw [AlphaFr.E2D.core_eq_of_isPGroup hd (isPGroup_of_inO2 hd hc.2.2 hO2)] at hy
    obtain ⟨s, hs, rfl⟩ := hy
    have hq : ∀ q : QuaternionGroup 2, q ^ 4 = 1 := by decide
    have h1 : (⟨s, hs⟩ : (S : Subgroup R)) ^ 4 = 1 := by
      have h2 := congrArg e.symm (hq (e ⟨s, hs⟩))
      rwa [map_pow, MulEquiv.symm_apply_apply, map_one] at h2
    have h3 := congrArg (fun z : (S : Subgroup R) => ((z : R) : Y)) h1
    simpa using h3
  rintro _ ⟨g, rfl⟩ x hx
  rw [mem_conjSub_iff] at hx
  calc x ^ 4 = (g * (g⁻¹ * x * g) * g⁻¹) ^ 4 := by group
    _ = g * (g⁻¹ * x * g) ^ 4 * g⁻¹ := conj_pow
    _ = 1 := by rw [hK _ hx]; group

theorem exists_mul_self_ne_one_mem (hd : TightDatum R S t) (hc : TightCls Y R S t) :
    ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ x ∈ L, x * x ≠ 1 := by
  obtain ⟨e⟩ : Nonempty ((S : Subgroup R) ≃* QuaternionGroup 2) := hc.1
  have hjK : ((e.symm (QuaternionGroup.a 1) : R) : Y) ∈ tightCore R :=
    hd.sylow_core.1 ⟨e.symm (.a 1), (e.symm (.a 1)).2, rfl⟩
  have hjj : ((e.symm (QuaternionGroup.a 1) : R) : Y) * ((e.symm (QuaternionGroup.a 1) : R) : Y)
      ≠ 1 := by
    intro h
    have h' : e.symm (QuaternionGroup.a 1 * QuaternionGroup.a 1) = 1 := by
      rw [map_mul]
      exact Subtype.ext (Subtype.ext h)
    rw [MulEquiv.map_eq_one_iff] at h'
    exact absurd h' (by decide)
  rintro _ ⟨g, rfl⟩
  refine ⟨g * ((e.symm (QuaternionGroup.a 1) : R) : Y) * g⁻¹, conj_mem_conjSub hjK, fun h => hjj ?_⟩
  calc ((e.symm (QuaternionGroup.a 1) : R) : Y) * ((e.symm (QuaternionGroup.a 1) : R) : Y)
      = g⁻¹ * ((g * ((e.symm (QuaternionGroup.a 1) : R) : Y) * g⁻¹) *
        (g * ((e.symm (QuaternionGroup.a 1) : R) : Y) * g⁻¹)) * g := by group
    _ = 1 := by rw [h]; group

section Phi

variable {m : ℕ} (φ : ↥(pSpan (CoreAssembly.conjClass (tightCore R))) →* AE.AEQ m)

theorem eq_of_phi_mem (hd : TightDatum R S t) (hc : TightCls Y R S t) (hO2 : TightInO2 t)
    (hm : 5 ≤ m) (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    (hlabel : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ (α : Finset (Fin m))
      (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α h b)
    {K J : Subgroup Y} (hK : K ∈ CoreAssembly.conjClass (tightCore R))
    (hJ : J ∈ CoreAssembly.conjClass (tightCore R)) {a : Y} (haK : a ∈ K) (ha2 : a * a ≠ 1)
    (haJ : φ ⟨a, le_pSpan hK haK⟩ ∈
      (J.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ) : K = J := by
  have htop : pSpan (CoreAssembly.conjClass (tightCore R)) = ⊤ := pSpan_eq_top hc
  have hZc : φ.ker.map (pSpan (CoreAssembly.conjClass (tightCore R))).subtype ≤
      Subgroup.center Y := by
    rintro _ ⟨k, hk, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro y
    have hy : y ∈ pSpan (CoreAssembly.conjClass (tightCore R)) := htop ▸ Subgroup.mem_top y
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp (hker hk) ⟨y, hy⟩)
  have hZK : ∀ L ∈ CoreAssembly.conjClass (tightCore R),
      φ.ker.map (pSpan (CoreAssembly.conjClass (tightCore R))).subtype ⊓ L = ⊥ := by
    intro L hL
    rw [eq_bot_iff]
    rintro x ⟨⟨k, hk, hkx⟩, hxL⟩
    obtain ⟨α, h, b, hlab⟩ := hlabel L hL
    have h8 : Nat.card ↥L = 8 := (card_mem hd hc hO2 L hL).trans (by norm_num)
    rw [Subgroup.mem_bot]
    refine phi_injOn φ hm hL h8 hlab hxL L.one_mem ?_
    have hk1 : φ k = 1 := hk
    have hk' : k = ⟨x, le_pSpan hL hxL⟩ := Subtype.ext hkx
    rw [← hk', hk1]
    exact (map_one φ).symm
  obtain ⟨⟨j, hjP⟩, hjJ, hja⟩ := haJ
  have hjJ' : j ∈ J := Subgroup.mem_subgroupOf.mp hjJ
  have hcZ : j⁻¹ * a ∈ φ.ker.map (pSpan (CoreAssembly.conjClass (tightCore R))).subtype := by
    refine ⟨⟨j, hjP⟩⁻¹ * ⟨a, le_pSpan hK haK⟩, ?_, rfl⟩
    show φ (⟨j, hjP⟩⁻¹ * ⟨a, le_pSpan hK haK⟩) = 1
    rw [map_mul, map_inv, hja, inv_mul_cancel]
  exact eq_of_mem_sup_center hd.hypOmegaGen (isPGroup_mem hd hc hO2) hZc hZK hK hJ haK ha2 hjJ'
    hcZ (by group)

theorem mem_omegaStarNbr_of_phi (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) (hm : 5 ≤ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    (hlabel : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ (α : Finset (Fin m))
      (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α h b)
    {L L' : Subgroup Y} (hL : L ∈ CoreAssembly.conjClass (tightCore R))
    (hL' : L' ∈ CoreAssembly.conjClass (tightCore R)) (hne : L ≠ L')
    {α β : Finset (Fin m)} {h : α.card = 4} {h' : β.card = 4} {b c : Bool}
    (hlab : (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar α h b)
    (hlab' : (L'.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
      AE.memBar β h' c)
    (hv : ∃ v ∈ AE.memBar β h' c, v * v ≠ 1 ∧
      ∀ a ∈ AE.memBar α h b, v * a * v⁻¹ ∈ AE.memBar α h b) :
    L' ∈ omegaStarNbr (CoreAssembly.conjClass (tightCore R)) L := by
  obtain ⟨v, hv, hvv, hvn⟩ := hv
  rw [← hlab'] at hv
  obtain ⟨⟨x, hxP⟩, hxL', rfl⟩ := hv
  have hxL : x ∈ L' := Subgroup.mem_subgroupOf.mp hxL'
  have hxx : x * x ≠ 1 := fun h1 => hvv (by
    rw [← map_mul, ← map_one φ]
    exact congrArg φ (Subtype.ext h1))
  have hx4 : orderOf x = 4 := by
    have := orderOf_eq_prime_pow (x := x) (p := 2) (n := 1) (by rw [pow_one, pow_two]; exact hxx)
      (by rw [show 2 ^ (1 + 1) = 4 by norm_num]; exact pow_four_eq_one hd hc hO2 L' hL' x hxL)
    simpa using this
  obtain ⟨l, hlL, hll⟩ := exists_mul_self_ne_one_mem hd hc L hL
  have hconjL : conjSub x L ∈ CoreAssembly.conjClass (tightCore R) :=
    hd.hypOmegaGen.conjInvariant x L hL
  have hxlx : x * l * x⁻¹ ∈ conjSub x L := conj_mem_conjSub hlL
  have hconj : conjSub x L = L := by
    refine eq_of_phi_mem φ hd hc hO2 hm hker hlabel hconjL hL hxlx ?_ ?_
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
          ↥(pSpan (CoreAssembly.conjClass (tightCore R)))) =
          ⟨x, hxP⟩ * ⟨l, le_pSpan hL hlL⟩ * (⟨x, hxP⟩)⁻¹ := rfl
      rw [h3, map_mul, map_mul, map_inv]
      exact h2
  have h2L' : IsPGroup 2 ↥L' := isPGroup_mem hd hc hO2 L' hL'
  refine ⟨hL', hne.symm, Subgroup.zpowers x, ?_, Subgroup.zpowers_le.mpr hxL,
    Subgroup.zpowers_le.mpr (mem_normalizer_iff_conjSub_eq.mpr hconj)⟩
  exact mem_USet_of_natCard hL' ⟨le_rfl, h2L', fun V hV _ hLV => le_antisymm hV hLV⟩
    (Subgroup.zpowers_le.mpr hxL) inferInstance
    (by rw [card_mem hd hc hO2 L' hL', Nat.card_zpowers, hx4]; norm_num)

theorem dstarConnected_of_phi (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) (hm : 5 ≤ m)
    (hker : φ.ker ≤ Subgroup.center ↥(pSpan (CoreAssembly.conjClass (tightCore R))))
    {𝒜 : Set (Finset (Fin m))} (h𝒜 : ∀ α ∈ 𝒜, α.card = 4)
    (hlabel : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ α ∈ 𝒜, ∃ (h : α.card = 4)
      (b : Bool),
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α h b)
    (hsurj : ∀ α ∈ 𝒜, ∀ (h : α.card = 4) (b : Bool), ∃ L ∈ CoreAssembly.conjClass (tightCore R),
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α h b)
    (hconn : ∀ α ∈ 𝒜, ∀ β ∈ 𝒜, Relation.ReflTransGen (fun γ δ => δ ∈ 𝒜 ∧ Adj4 γ δ) α β) :
    T3.DStarConnected (CoreAssembly.conjClass (tightCore R)) := by
  have hlabel' : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∃ (α : Finset (Fin m))
      (h : α.card = 4) (b : Bool),
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α h b :=
    fun L hL => by
      obtain ⟨α, -, h, b, hlab⟩ := hlabel L hL
      exact ⟨α, h, b, hlab⟩
  have hsame : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ M ∈ CoreAssembly.conjClass
      (tightCore R),
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
        (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ → L = M := by
    intro L hL M hM hLM
    obtain ⟨a, haL, ha2⟩ := exists_mul_self_ne_one_mem hd hc L hL
    refine eq_of_phi_mem φ hd hc hO2 hm hker hlabel' hL hM haL ha2 ?_
    rw [← hLM]
    exact ⟨⟨a, le_pSpan hL haL⟩, Subgroup.mem_subgroupOf.mpr haL, rfl⟩
  have hstep : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ L' ∈ CoreAssembly.conjClass
      (tightCore R), ∀ {α β : Finset (Fin m)} {h : α.card = 4} {h' : β.card = 4} {b c : Bool},
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α h b →
      (L'.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
        AE.memBar β h' c →
      (∃ v ∈ AE.memBar β h' c, v * v ≠ 1 ∧
        ∀ a ∈ AE.memBar α h b, v * a * v⁻¹ ∈ AE.memBar α h b) →
      Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass (tightCore R))) L L' ∧
        Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass (tightCore R))) L' L := by
    intro L hL L' hL' α β h h' b c hlab hlab' hv
    by_cases hLL : L = L'
    · subst hLL
      exact ⟨Relation.ReflTransGen.refl, Relation.ReflTransGen.refl⟩
    · have h1 := mem_omegaStarNbr_of_phi φ hd hc hO2 hm hker hlabel' hL hL' hLL hlab hlab' hv
      exact ⟨Relation.ReflTransGen.single ⟨hL', Or.inl h1⟩,
        Relation.ReflTransGen.single ⟨hL, Or.inr h1⟩⟩
  have hto : ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ M ∈ CoreAssembly.conjClass
      (tightCore R), ∀ {α : Finset (Fin m)} {h : α.card = 4} {b : Bool},
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ = AE.memBar α h b →
      (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
        AE.memBar α h true →
      Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass (tightCore R))) L M ∧
        Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass (tightCore R))) M L := by
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
      ∀ L ∈ CoreAssembly.conjClass (tightCore R), ∀ (h : α.card = 4),
      (L.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
        AE.memBar α h true →
      β ∈ 𝒜 ∧ ∀ M ∈ CoreAssembly.conjClass (tightCore R), ∀ (h' : β.card = 4),
        (M.subgroupOf (pSpan (CoreAssembly.conjClass (tightCore R)))).map φ =
          AE.memBar β h' true →
        Relation.ReflTransGen (dstarAdj (CoreAssembly.conjClass (tightCore R))) L M := by
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

theorem dstarConnected_of_aeIdent (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t) {m : ℕ} (hm : 6 ≤ m)
    (I : AEIdent (CoreAssembly.conjClass (tightCore R)) m) :
    T3.DStarConnected (CoreAssembly.conjClass (tightCore R)) := by
  refine dstarConnected_of_phi I.φ hd hc hO2 (by omega) I.ker_le (𝒜 := {α | α.card = 4})
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

theorem dstarConnected_of_e64 (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t)
    (I : AEIdentOn (CoreAssembly.conjClass (tightCore R)) 7 AE.e64Sets AE.e64Sub) :
    T3.DStarConnected (CoreAssembly.conjClass (tightCore R)) := by
  refine dstarConnected_of_phi I.φ hd hc hO2 (by norm_num) I.ker_le
    (fun α hα => card_of_mem_e64Sets hα) I.label (fun α hα h b => I.label_surj α hα h b)
    (fun α hα β hβ => ?_)
  by_cases hαβ : α = β
  · subst hαβ
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨hβ, adj4_of_mem_e64Sets hα hβ hαβ⟩

theorem dstarConnected_of_e29 (hd : TightDatum R S t) (hc : TightCls Y R S t)
    (hO2 : TightInO2 t)
    (I : AEIdentOn (CoreAssembly.conjClass (tightCore R)) 8 AE.e29Sets AE.e29Sub) :
    T3.DStarConnected (CoreAssembly.conjClass (tightCore R)) := by
  refine dstarConnected_of_phi I.φ hd hc hO2 (by norm_num) I.ker_le
    (fun α hα => card_of_mem_e29Sets hα) I.label (fun α hα h b => I.label_surj α hα h b)
    (fun α hα β hβ => ?_)
  by_cases hαβ : α = β
  · subst hαβ
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨hβ, adj4_of_mem_e29Sets hα hβ hαβ⟩

end CFSG.ClassicalInvolution.Q3.TL4.SecIdE2
