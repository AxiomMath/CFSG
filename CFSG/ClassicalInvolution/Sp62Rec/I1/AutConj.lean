module

public import CFSG.ClassicalInvolution.Q3.TL4AECover
import CFSG.ClassicalInvolution.Q3.TL4AE286Aut
import CFSG.ClassicalInvolution.Q3.TL4Mdl117

public section

namespace CFSG.ClassicalInvolution.Sp62Rec.I1

open CFSG CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
  CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
  CFSG.ClassicalInvolution.Q3.AE.Wr

section Abstract

variable {X : Type} [Group X] [Finite X] {Φ : Set (Subgroup X)}

theorem isUniqueInvolution_map_mulEquiv {K : Subgroup X} {z : X} (h : IsUniqueInvolution K z)
    (α : X ≃* X) : IsUniqueInvolution (K.map α.toMonoidHom) (α z) where
  mem := ⟨z, h.mem, rfl⟩
  ne_one := fun h1 => h.ne_one (α.injective (by rw [h1, map_one]))
  sq := by rw [← map_mul, h.sq, map_one]
  unique := by
    rintro _ ⟨y, hy, rfl⟩ hsq
    have hsq' : α y * α y = 1 := hsq
    have : y * y = 1 := α.injective (by rw [map_mul, hsq', map_one])
    rcases h.unique y hy this with h1 | h1
    · left; show α y = 1; rw [h1, map_one]
    · right; show α y = α z; rw [h1]

theorem twin_labels_abs {I : AEIdent Φ 6} (hH : TL4.AECoverHyp I) {K K' : Subgroup X}
    (hK : K ∈ Φ) (hK' : K' ∈ Φ) (hne : K' ≠ K) {z : X} (hzK : IsUniqueInvolution K z)
    (hzK' : IsUniqueInvolution K' z) :
    ∃ (β : Finset (Fin 6)) (hβ : β.card = 4) (b : Bool),
      (K.subgroupOf (pSpan Φ)).map I.φ = memBar β hβ b ∧
      (K'.subgroupOf (pSpan Φ)).map I.φ = memBar β hβ (!b) := by
  obtain ⟨δ, hδ, c, hlab⟩ := I.label K hK
  obtain ⟨γ, hγ, c', hlab'⟩ := I.label K' hK'
  have e1 := I.map_eq_zBar (by norm_num) hK (hH.card _ hK) hlab hzK
  have e2 := I.map_eq_zBar (by norm_num) hK' (hH.card _ hK') hlab' hzK'
  have hγδ : γ = δ := AE.eq_of_zBar_eq (by norm_num) (e2.symm.trans e1)
  subst hγδ
  have hc'c : c' = !c := by
    by_contra hcc
    have : c' = c := by cases c <;> cases c' <;> simp_all
    subst this
    exact hne (hH.label_inj _ hK' _ hK (hlab'.trans hlab.symm))
  exact ⟨γ, hγ, c, hlab, by rw [hlab', hc'c]⟩

theorem eq_or_eq_of_involution {I : AEIdent Φ 6} (hH : TL4.AECoverHyp I) {K K' : Subgroup X}
    (hK : K ∈ Φ) (hK' : K' ∈ Φ) (hne : K' ≠ K) {z : X} (hzK : IsUniqueInvolution K z)
    (hzK' : IsUniqueInvolution K' z) {M : Subgroup X} (hM : M ∈ Φ)
    (hzM : IsUniqueInvolution M z) : M = K ∨ M = K' := by
  obtain ⟨β, hβ, b, hlab, hlab'⟩ := twin_labels_abs hH hK hK' hne hzK hzK'
  obtain ⟨β', hβ', d, hlabM⟩ := I.label M hM
  have e1 := I.map_eq_zBar (by norm_num) hK (hH.card _ hK) hlab hzK
  have e3 := I.map_eq_zBar (by norm_num) hM (hH.card _ hM) hlabM hzM
  have hββ' : β' = β := AE.eq_of_zBar_eq (by norm_num) (e3.symm.trans e1)
  subst hββ'
  cases b <;> cases d
  · exact Or.inl (hH.label_inj _ hM _ hK (hlabM.trans hlab.symm))
  · exact Or.inr (hH.label_inj _ hM _ hK' (hlabM.trans (by simpa using hlab'.symm)))
  · exact Or.inr (hH.label_inj _ hM _ hK' (hlabM.trans (by simpa using hlab'.symm)))
  · exact Or.inl (hH.label_inj _ hM _ hK (hlabM.trans hlab.symm))

theorem aut_fixes_twins {I : AEIdent Φ 6} (hH : TL4.AECoverHyp I) {K K' : Subgroup X}
    (hK : K ∈ Φ) (hK' : K' ∈ Φ) (hne : K' ≠ K) {z : X} (hzK : IsUniqueInvolution K z)
    (hzK' : IsUniqueInvolution K' z) (α : X ≃* X)
    (hαΦ : ∀ L ∈ Φ, L.map α.toMonoidHom ∈ Φ) (hαz : α z = z)
    (hodd : ∀ y ∈ K, Odd (orderOf (α y * y⁻¹))) (hodd' : ∀ y ∈ K', Odd (orderOf (α y * y⁻¹))) :
    ∀ y ∈ K ⊔ K', α y = y := by
  have hperm : ∀ L, (L = K ∨ L = K') →
      ((L.map α.toMonoidHom) = K ∨ (L.map α.toMonoidHom) = K') := by
    intro L hL
    have hLΦ : L ∈ Φ := by rcases hL with rfl | rfl <;> assumption
    have hLz : IsUniqueInvolution L z := by rcases hL with rfl | rfl <;> assumption
    have := isUniqueInvolution_map_mulEquiv hLz α
    rw [hαz] at this
    exact eq_or_eq_of_involution hH hK hK' hne hzK hzK' (hαΦ L hLΦ) this
  obtain ⟨β, hβ, b, hlab, hlab'⟩ := twin_labels_abs hH hK hK' hne hzK hzK'
  have hcomm : ∀ x ∈ K, ∀ y ∈ K', x * y = y * x := by
    cases b
    · intro x hx y hy
      exact (hH.twin_comm β hβ K' hK' K hK hlab' hlab y hy x hx).symm
    · intro x hx y hy
      exact hH.twin_comm β hβ K hK K' hK' hlab hlab' x hx y hy
  have h8K := hH.card K hK
  have h8K' := hH.card K' hK'
  have hpow : ∀ (L : Subgroup X), Nat.card L = 8 → ∀ x ∈ L, x ^ 8 = 1 := by
    intro L hL x hx
    have := pow_card_eq_one' (G := ↥L) (x := ⟨x, hx⟩)
    rw [hL] at this
    exact congrArg Subtype.val this
  have hfix : ∀ (L M : Subgroup X), Nat.card L = 8 → Nat.card M = 8 →
      (L = M ∨ ∀ x ∈ M, ∀ y ∈ L, x * y = y * x) → (∀ y ∈ L, α y ∈ M) →
      (∀ y ∈ L, Odd (orderOf (α y * y⁻¹))) → ∀ y ∈ L, α y = y := by
    intro L M hL hM hLM hmap hodd' y hy
    have hord : (α y * y⁻¹) ^ 8 = 1 := by
      rcases hLM with rfl | hc
      · exact hpow L hL _ (L.mul_mem (hmap y hy) (L.inv_mem hy))
      · have hcm : Commute (α y) y⁻¹ :=
          hc _ (hmap y hy) _ (L.inv_mem hy)
        rw [hcm.mul_pow, hpow M hM _ (hmap y hy), inv_pow, hpow L hL _ hy, inv_one, mul_one]
    have h1 : orderOf (α y * y⁻¹) ∣ 8 := orderOf_dvd_of_pow_eq_one hord
    have h2 : orderOf (α y * y⁻¹) = 1 := by
      have : orderOf (α y * y⁻¹) ∣ 2 ^ 3 := by simpa using h1
      obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 this
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · simpa using hi
      · exfalso
        have := hodd' y hy
        rw [hi] at this
        exact (Nat.not_even_iff_odd.mpr this) (Nat.even_pow.mpr ⟨even_two, hipos.ne'⟩)
    have : α y * y⁻¹ = 1 := orderOf_eq_one_iff.mp h2
    exact mul_inv_eq_one.mp this
  have hKfix : ∀ y ∈ K, α y = y := by
    have hm : ∀ y ∈ K, α y ∈ K.map α.toMonoidHom := fun y hy => ⟨y, hy, rfl⟩
    rcases hperm K (Or.inl rfl) with h | h
    · exact hfix K K h8K h8K (Or.inl rfl) (fun y hy => h ▸ hm y hy) hodd
    · exact hfix K K' h8K h8K' (Or.inr (fun x hx y hy => (hcomm y hy x hx).symm))
        (fun y hy => h ▸ hm y hy) hodd
  have hK'fix : ∀ y ∈ K', α y = y := by
    have hm : ∀ y ∈ K', α y ∈ K'.map α.toMonoidHom := fun y hy => ⟨y, hy, rfl⟩
    rcases hperm K' (Or.inr rfl) with h | h
    · exact hfix K' K h8K' h8K (Or.inr (fun x hx y hy => hcomm x hx y hy))
        (fun y hy => h ▸ hm y hy) hodd'
    · exact hfix K' K' h8K' h8K' (Or.inl rfl) (fun y hy => h ▸ hm y hy) hodd'
  have hle : K ⊔ K' ≤ MonoidHom.eqLocus α.toMonoidHom (MonoidHom.id X) :=
    sup_le (fun y hy => hKfix y hy) (fun y hy => hK'fix y hy)
  exact fun y hy => hle hy

theorem mem_piSub_central {c : Wr 6} (hc : c ∈ piSub 6) (a : Wr 6) : c * a = a * c := by
  rcases mem_piSub.mp hc with rfl | rfl
  · rw [one_mul, mul_one]
  · exact allOnes_comm a

theorem exists_conj_of_aut (I : AEIdent Φ 6)
    (hperf : Group.IsPerfect ↥(pSpan Φ))
    (ψ : ↥(pSpan Φ) ≃* ↥(aeSub 6)) (hψ : ∀ x : ↥(pSpan Φ), mkQ 6 (ψ x : Wr 6) = I.φ x)
    (α : MulAut ↥(pSpan Φ))
    (hα : ∀ L ∈ Φ, ∃ L' ∈ Φ,
      (L.subgroupOf (pSpan Φ)).map α.toMonoidHom = L'.subgroupOf (pSpan Φ)) :
    ∃ w : Wr 6, ∀ x : ↥(pSpan Φ), (ψ (α x) : Wr 6) = w * (ψ x : Wr 6) * w⁻¹ := by
  have hm : 5 ≤ 6 := by norm_num
  set β := I.inducedAutOf hm α with hβ
  have hperm : ∀ (δ : Finset (Fin 6)) (h : δ.card = 4) (b : Bool),
      ∃ (δ' : Finset (Fin 6)) (h' : δ'.card = 4) (b' : Bool),
        ((AE.memBar δ h b).subgroupOf ((AE.aeSub 6).map (AE.mkQ 6))).map β.toMonoidHom =
          (AE.memBar δ' h' b').subgroupOf ((AE.aeSub 6).map (AE.mkQ 6)) := by
    intro δ h b
    obtain ⟨L, hL, hlab⟩ := I.label_surj δ h b
    obtain ⟨L', hL', hLL'⟩ := hα L hL
    obtain ⟨δ', h', b', hlab₂⟩ := I.label L' hL'
    refine ⟨δ', h', b', ?_⟩
    have hle : ((AE.memBar δ h b).subgroupOf ((AE.aeSub 6).map (AE.mkQ 6))).map β.toMonoidHom ≤
        (AE.memBar δ' h' b').subgroupOf ((AE.aeSub 6).map (AE.mkQ 6)) := by
      intro z hz
      obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hz
      rw [Subgroup.mem_subgroupOf] at hg ⊢
      rw [← hlab] at hg
      obtain ⟨l, hl, hlg⟩ := hg
      have hgl : g = I.toModel l := Subtype.ext hlg.symm
      rw [hgl, MulEquiv.coe_toMonoidHom, hβ, I.inducedAutOf_apply hm, ← hlab₂]
      refine Subgroup.mem_map.mpr ⟨α l, ?_, rfl⟩
      rw [← hLL']
      exact Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
    refine Subgroup.eq_of_le_of_card_ge hle (le_of_eq ?_)
    rw [Subgroup.card_map_of_injective (fun a b hab => β.injective hab),
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (memBar_le_aeModel δ' h' b')).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (memBar_le_aeModel δ h b)).toEquiv,
      AE.natCard_memBar hm, AE.natCard_memBar hm]
  obtain ⟨x₀, hx₀⟩ := TL4.model117_proved 6 hm (by norm_num) β hperm
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective x₀
  refine ⟨w, ?_⟩
  have key : ∀ x : ↥(pSpan Φ),
      ((w * (ψ x : Wr 6) * w⁻¹)⁻¹ * (ψ (α x) : Wr 6)) ∈ piSub 6 := by
    intro x
    have h1 : I.φ (α x) = mkQ 6 w * I.φ x * (mkQ 6 w)⁻¹ := by
      have := hx₀ (I.toModel x)
      rw [hβ, I.inducedAutOf_apply hm α x] at this
      exact this
    have h2 : mkQ 6 (ψ (α x) : Wr 6) = mkQ 6 (w * (ψ x : Wr 6) * w⁻¹) := by
      rw [hψ, h1, map_mul, map_mul, map_inv, hψ]
    have h3 := mkQ_eq_iff.mp h2
    have : ((w * (ψ x : Wr 6) * w⁻¹)⁻¹ * (ψ (α x) : Wr 6)) =
        ((ψ (α x) : Wr 6)⁻¹ * (w * (ψ x : Wr 6) * w⁻¹))⁻¹ := by group
    rw [this]
    refine (piSub 6).inv_mem ?_
    rcases h3 with h | h
    · rw [h]; exact (piSub 6).one_mem
    · rw [h]; exact mem_piSub.mpr (Or.inr rfl)
  let D : ↥(pSpan Φ) →* Wr 6 :=
    MonoidHom.mk' (fun x => (w * (ψ x : Wr 6) * w⁻¹)⁻¹ * (ψ (α x) : Wr 6))
    (by
      intro x y
      have hcx := mem_piSub_central (key x)
      simp only [map_mul, Subgroup.coe_mul]
      have e1 : w * ((ψ x : Wr 6) * (ψ y : Wr 6)) * w⁻¹ =
          (w * (ψ x : Wr 6) * w⁻¹) * (w * (ψ y : Wr 6) * w⁻¹) := by group
      rw [e1]
      calc ((w * (ψ x : Wr 6) * w⁻¹) * (w * (ψ y : Wr 6) * w⁻¹))⁻¹ *
            ((ψ (α x) : Wr 6) * (ψ (α y) : Wr 6))
          = (w * (ψ y : Wr 6) * w⁻¹)⁻¹ * ((w * (ψ x : Wr 6) * w⁻¹)⁻¹ * (ψ (α x) : Wr 6)) *
              (ψ (α y) : Wr 6) := by group
        _ = ((w * (ψ x : Wr 6) * w⁻¹)⁻¹ * (ψ (α x) : Wr 6)) *
              (w * (ψ y : Wr 6) * w⁻¹)⁻¹ * (ψ (α y) : Wr 6) := by
            rw [← hcx ((w * (ψ y : Wr 6) * w⁻¹)⁻¹)]
        _ = ((w * (ψ x : Wr 6) * w⁻¹)⁻¹ * (ψ (α x) : Wr 6)) *
              ((w * (ψ y : Wr 6) * w⁻¹)⁻¹ * (ψ (α y) : Wr 6)) := by group)
  have hD : ∀ x, D x = 1 := by
    have hcomm : commutator ↥(pSpan Φ) ≤ D.ker := by
      rw [commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv]
      have hcab : D a * D b = D b * D a := mem_piSub_central (key a) (D b)
      calc D a * D b * (D a)⁻¹ * (D b)⁻¹ = D b * D a * (D a)⁻¹ * (D b)⁻¹ := by rw [hcab]
        _ = 1 := by group
    intro x
    exact MonoidHom.mem_ker.mp (hcomm (hperf.commutator_eq_top ▸ Subgroup.mem_top x))
  intro x
  exact (inv_mul_eq_one.mp (hD x)).symm

theorem exists_restrict_aut (hgen : pSpan Φ = ⊤) (α : X ≃* X)
    (hαΦ : ∀ L ∈ Φ, L.map α.toMonoidHom ∈ Φ) :
    ∃ αP : MulAut ↥(pSpan Φ), (∀ x : ↥(pSpan Φ), ((αP x : ↥(pSpan Φ)) : X) = α (x : X)) ∧
      ∀ L ∈ Φ, ∃ L' ∈ Φ,
        (L.subgroupOf (pSpan Φ)).map αP.toMonoidHom = L'.subgroupOf (pSpan Φ) := by
  let eqTop : ↥(pSpan Φ) ≃* X := (MulEquiv.subgroupCongr hgen).trans Subgroup.topEquiv
  have hc : ∀ x : ↥(pSpan Φ), ((eqTop x : X)) = (x : X) := fun x => rfl
  have hc' : ∀ z : X, ((eqTop.symm z : ↥(pSpan Φ)) : X) = z := fun z => rfl
  let αP : MulAut ↥(pSpan Φ) := eqTop.trans (α.trans eqTop.symm)
  have hαP : ∀ x : ↥(pSpan Φ), ((αP x : ↥(pSpan Φ)) : X) = α (x : X) := fun x => by
    show ((eqTop.symm (α (eqTop x)) : ↥(pSpan Φ)) : X) = α (x : X)
    rw [hc', hc]
  refine ⟨αP, hαP, fun L hL => ⟨L.map α.toMonoidHom, hαΦ L hL, ?_⟩⟩
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' := Subgroup.mem_subgroupOf.mp hx
    refine Subgroup.mem_subgroupOf.mpr ?_
    show ((αP x : ↥(pSpan Φ)) : X) ∈ Subgroup.map α.toMonoidHom L
    rw [hαP]
    exact ⟨_, hx', rfl⟩
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨l, hl, hly⟩ := hy
    have hlP : l ∈ pSpan Φ := hgen ▸ Subgroup.mem_top l
    refine ⟨⟨l, hlP⟩, Subgroup.mem_subgroupOf.mpr hl, ?_⟩
    apply Subtype.ext
    show ((αP ⟨l, hlP⟩ : ↥(pSpan Φ)) : X) = (y : X)
    rw [hαP]
    exact hly

theorem psi_eq_allOnes (I : AEIdent Φ 6) (ψ : ↥(pSpan Φ) ≃* ↥(aeSub 6))
    (hψ : ∀ x : ↥(pSpan Φ), mkQ 6 (ψ x : Wr 6) = I.φ x) {c : ↥(pSpan Φ)} (hc : c ∈ I.φ.ker)
    (hc1 : c ≠ 1) : (ψ c : Wr 6) = allOnes 6 := by
  have h1 : mkQ 6 (ψ c : Wr 6) = 1 := by rw [hψ]; exact hc
  have h2 : (ψ c : Wr 6) ∈ piSub 6 := (QuotientGroup.eq_one_iff _).mp h1
  rcases mem_piSub.mp h2 with h | h
  · exfalso
    apply hc1
    exact ψ.injective ((Subtype.ext h).trans (map_one ψ).symm)
  · exact h

end Abstract

end CFSG.ClassicalInvolution.Sp62Rec.I1
