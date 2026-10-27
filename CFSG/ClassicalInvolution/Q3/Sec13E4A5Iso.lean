module

public import CFSG.ClassicalInvolution.Q3.Sec13E4A5Q

public section

namespace CFSG.ClassicalInvolution.Q3.Sec13

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.QuasithinUnique

section Wreath

open AE

private theorem wr_ofVec_add {n : ℕ} (x y : Fin n → ZMod 2) :
    Wr.ofVec (x + y) = Wr.ofVec x * Wr.ofVec y := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show (x + y) i = x i + y ((1 : Equiv.Perm (Fin n)).symm i)
    rfl
  · show (1 : Equiv.Perm (Fin n)) = 1 * 1
    rw [one_mul]

private theorem wr_ofPerm_mul {n : ℕ} (σ τ : Equiv.Perm (Fin n)) :
    Wr.ofPerm (σ * τ) = Wr.ofPerm σ * Wr.ofPerm τ := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show (0 : ZMod 2) = 0 + 0
    rw [add_zero]
  · rfl

private theorem wr_ofPerm_conj {n : ℕ} (σ : Equiv.Perm (Fin n)) (v : Fin n → ZMod 2) :
    Wr.ofPerm σ * Wr.ofVec v * (Wr.ofPerm σ)⁻¹ = Wr.ofVec (fun i => v (σ.symm i)) := by
  refine Wr.ext (funext fun i => ?_) ?_
  · show (0 + v (σ.symm i)) + 0 = v (σ.symm i)
    simp
  · show σ * 1 * σ⁻¹ = 1
    simp

private theorem wr_mkQ_ofVec_eq_one_iff {n : ℕ} (v : Fin n → ZMod 2) :
    mkQ n (Wr.ofVec v) = 1 ↔ v = 0 ∨ v = fun _ => 1 := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_piSub]
  constructor
  · rintro (h | h)
    · exact Or.inl (congrArg Wr.vec h)
    · exact Or.inr (congrArg Wr.vec h)
  · rintro (h | h)
    · exact Or.inl (Wr.ext h rfl)
    · exact Or.inr (Wr.ext h rfl)

private def wrOfVecHom (n : ℕ) : Multiplicative (Fin n → ZMod 2) →* Wr n where
  toFun f := Wr.ofVec f.toAdd
  map_one' := rfl
  map_mul' f g := wr_ofVec_add f.toAdd g.toAdd

private def wrOfPermHom (n : ℕ) : Equiv.Perm (Fin n) →* Wr n where
  toFun σ := Wr.ofPerm σ
  map_one' := rfl
  map_mul' σ τ := wr_ofPerm_mul σ τ

private def vecQ : Multiplicative (Fin 5 → ZMod 2) →* AEQ 5 := (mkQ 5).comp (wrOfVecHom 5)

private def permQ : Equiv.Perm (Fin 5) →* AEQ 5 := (mkQ 5).comp (wrOfPermHom 5)

private theorem vecQ_eq_one_iff (f : Multiplicative (Fin 5 → ZMod 2)) :
    vecQ f = 1 ↔ f.toAdd = 0 ∨ f.toAdd = fun _ => 1 :=
  wr_mkQ_ofVec_eq_one_iff f.toAdd

private theorem permQ_conj_vecQ (σ : Equiv.Perm (Fin 5)) (f : Multiplicative (Fin 5 → ZMod 2)) :
    permQ σ * vecQ f * (permQ σ)⁻¹ =
      vecQ (Multiplicative.ofAdd (fun i => f.toAdd (σ.symm i))) := by
  show mkQ 5 (Wr.ofPerm σ) * mkQ 5 (Wr.ofVec f.toAdd) * (mkQ 5 (Wr.ofPerm σ))⁻¹ =
    mkQ 5 (Wr.ofVec (fun i => f.toAdd (σ.symm i)))
  rw [← map_inv, ← map_mul, ← map_mul, wr_ofPerm_conj]

private theorem eq_one_of_vecQ_mul_permQ (f : Multiplicative (Fin 5 → ZMod 2))
    (σ : Equiv.Perm (Fin 5)) (h : vecQ f * permQ σ = 1) : σ = 1 := by
  have h' : mkQ 5 (Wr.ofVec f.toAdd * Wr.ofPerm σ) = 1 := by
    rw [map_mul]
    exact h
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_piSub] at h'
  rcases h' with h' | h'
  · simpa [Wr.mul_perm, Wr.one_perm, Wr.ofVec, Wr.ofPerm] using congrArg Wr.perm h'
  · simpa [Wr.mul_perm, Wr.one_perm, Wr.ofVec, Wr.ofPerm, Wr.allOnes] using congrArg Wr.perm h'

private theorem vecQ_mem (f : Multiplicative (Fin 5 → ZMod 2)) : vecQ f ∈ TL4.aeModel 5 := by
  have hs : ∀ t : ZMod 2, t = 0 ∨ t + 5 = 0 := by decide
  rcases hs (∑ i, f.toAdd i) with h0 | h1
  · exact ⟨Wr.ofVec f.toAdd, ⟨h0, Equiv.Perm.sign_one⟩, rfl⟩
  · refine ⟨Wr.ofVec (f.toAdd + fun _ => 1), ⟨?_, Equiv.Perm.sign_one⟩, ?_⟩
    · simp only [Fin.sum_univ_five] at h1
      simp only [Wr.wsum, Wr.ofVec, Fin.sum_univ_five, Pi.add_apply]
      linear_combination h1
    · show mkQ 5 (Wr.ofVec (f.toAdd + fun _ => 1)) = mkQ 5 (Wr.ofVec f.toAdd)
      rw [wr_ofVec_add, map_mul,
        (wr_mkQ_ofVec_eq_one_iff (fun _ : Fin 5 => (1 : ZMod 2))).mpr (Or.inr rfl), mul_one]

private theorem permQ_mem {σ : Equiv.Perm (Fin 5)} (hσ : σ ∈ alternatingGroup (Fin 5)) :
    permQ σ ∈ TL4.aeModel 5 :=
  ⟨Wr.ofPerm σ, ⟨by simp [Wr.wsum, Wr.ofPerm], Equiv.Perm.mem_alternatingGroup.mp hσ⟩, rfl⟩

end Wreath

private theorem iso_exists_lift_range {X Y M : Type*} [Group X] [Group Y] [Group M] (β : X →* Y)
    (S : Subgroup Y) (hS : β.range = S) (ψ₀ : X →* M) (hker : β.ker ≤ ψ₀.ker) :
    ∃ ψ : S →* M, ∀ (x : X) (hx : β x ∈ S), ψ ⟨β x, hx⟩ = ψ₀ x := by
  have hmem : ∀ x, β x ∈ S := fun x => by
    rw [← hS]
    exact ⟨x, rfl⟩
  let β' : X →* S := β.codRestrict S hmem
  have hsurj : Function.Surjective β' := by
    rintro ⟨s, hs⟩
    have hs' : s ∈ β.range := by
      rw [hS]
      exact hs
    obtain ⟨x, hx⟩ := hs'
    exact ⟨x, Subtype.ext hx⟩
  have hk : β'.ker ≤ ψ₀.ker := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker] at hx ⊢
    exact congrArg Subtype.val hx
  refine ⟨β'.liftOfSurjective hsurj ⟨ψ₀, hk⟩, fun x hx => ?_⟩
  exact MonoidHom.liftOfRightInverse_comp_apply β' _ (Function.rightInverse_surjInv hsurj)
    ⟨ψ₀, hk⟩ x

private theorem iso_exists_mul_eq {X : Type*} [Group X] {Q H : Subgroup X} [Q.Normal]
    (hQH : Q.IsComplement' H) (g : X) : ∃ (q : Q) (x : H), (q : X) * (x : X) = g := by
  obtain ⟨y, hy⟩ := (SemidirectProduct.mulEquivSubgroup hQH).surjective g
  exact ⟨y.left, y.right, by rwa [SemidirectProduct.mulEquivSubgroup_apply] at hy⟩

private theorem iso_exists_hom_of_isComplement {X M : Type*} [Group X] [Group M] {Q H : Subgroup X}
    [Q.Normal] (hQH : Q.IsComplement' H) (ψ : Q →* M) (τ : H →* M)
    (hc : ∀ (x : H) (q : Q) (hq : (x : X) * q * (x : X)⁻¹ ∈ Q),
      τ x * ψ q * (τ x)⁻¹ = ψ ⟨(x : X) * q * (x : X)⁻¹, hq⟩) :
    ∃ φ : X →* M, (∀ q : Q, φ q = ψ q) ∧ ∀ x : H, φ x = τ x := by
  let e := SemidirectProduct.mulEquivSubgroup hQH
  refine ⟨(SemidirectProduct.lift ψ τ ?_).comp e.symm.toMonoidHom, ?_, ?_⟩
  · intro x
    ext q
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [hc x q (Subgroup.Normal.conj_mem inferInstance (q : X) q.2 (x : X))]
    congr 1
  · intro q
    have h1 : e.symm (q : X) = SemidirectProduct.inl q := by
      rw [MulEquiv.symm_apply_eq]
      simp [e, SemidirectProduct.mulEquivSubgroup_apply]
    simp [h1]
  · intro x
    have h1 : e.symm (x : X) = SemidirectProduct.inr x := by
      rw [MulEquiv.symm_apply_eq]
      simp [e, SemidirectProduct.mulEquivSubgroup_apply]
    simp [h1]

private theorem iso_isUniqueInvolution_map {X M : Type*} [Group X] [Group M] {K : Subgroup X}
    {z : X} (hz : IsUniqueInvolution K z) {φ : X →* M} (hφ : Function.Injective φ) :
    IsUniqueInvolution (K.map φ) (φ z) where
  mem := Subgroup.mem_map_of_mem φ hz.mem
  ne_one := fun h1 => hz.ne_one (hφ (by rw [h1, map_one]))
  sq := by rw [← map_mul, hz.sq, map_one]
  unique := by
    rintro y ⟨l, hl, rfl⟩ hy2
    rw [← map_mul, ← map_one φ] at hy2
    rcases hz.unique l hl (hφ hy2) with rfl | rfl
    · exact Or.inl (map_one φ)
    · exact Or.inr rfl

private theorem iso_map_conjSub {X M : Type*} [Group X] [Group M] (φ : X →* M) (g : X)
    (K : Subgroup X) :
    (conjSub g K).map φ = (K.map φ).map (MulAut.conj (φ g)).toMonoidHom := by
  unfold conjSub
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext k
  simp [MulAut.conj_apply]

private theorem iso_card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin, Nat.factorial]

variable {G : Type} [Group G] [Finite G]

namespace E4Hyp

variable {Ω : Set (Subgroup G)} {W : Subgroup G} (h : E4Hyp Ω W)
include h

theorem exists_hom (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5)) {H : Subgroup G}
    (hH : (pCore 2 G).IsComplement' H) :
    ∃ φ : G →* AE.AEQ 5, Function.Injective φ ∧ φ.range = TL4.aeModel 5 := by
  have hrange : (h.beta a).range = pCore 2 G := h.range_beta_eq a
  have hkerβ := h.beta_eq_one_iff a
  obtain ⟨ψ, hψ⟩ := iso_exists_lift_range (h.beta a) (pCore 2 G) hrange vecQ (fun f hf =>
    MonoidHom.mem_ker.mpr ((vecQ_eq_one_iff f).mpr ((hkerβ f).mp (MonoidHom.mem_ker.mp hf))))
  let τ : H →* AE.AEQ 5 := permQ.comp ((sig a).comp H.subtype)
  have hτ : ∀ x : H, τ x = permQ (sig a x) := fun x => rfl
  have hψτ : ∀ q : pCore 2 G, ∃ f, ψ q = vecQ f ∧ h.beta a f = q := by
    rintro ⟨q, hq⟩
    obtain ⟨f, rfl⟩ : q ∈ (h.beta a).range := by
      rw [hrange]
      exact hq
    exact ⟨f, hψ f hq, rfl⟩
  have hcompat : ∀ (x : H) (q : pCore 2 G) (hq : (x : G) * q * (x : G)⁻¹ ∈ pCore 2 G),
      τ x * ψ q * (τ x)⁻¹ = ψ ⟨(x : G) * q * (x : G)⁻¹, hq⟩ := by
    intro x q hq
    obtain ⟨f, hf, hfq⟩ := hψτ q
    have e1 : (x : G) * q * (x : G)⁻¹ =
        h.beta a (Multiplicative.ofAdd (fun γ => f.toAdd ((sig a x).symm γ))) := by
      rw [← hfq]
      exact h.conj_beta a x f
    have e2 : (⟨(x : G) * q * (x : G)⁻¹, hq⟩ : pCore 2 G) =
        ⟨h.beta a (Multiplicative.ofAdd (fun γ => f.toAdd ((sig a x).symm γ))),
          by rw [← e1]; exact hq⟩ := Subtype.ext e1
    rw [e2, hψ (Multiplicative.ofAdd (fun γ => f.toAdd ((sig a x).symm γ))) _, hf, hτ]
    exact permQ_conj_vecQ _ f
  obtain ⟨φ, hφq, hφx⟩ := iso_exists_hom_of_isComplement hH ψ τ hcompat
  have hφ : ∀ (q : pCore 2 G) (x : H), φ ((q : G) * x) = ψ q * τ x := by
    intro q x
    rw [map_mul, hφq, hφx]
  have hψinj : ∀ q : pCore 2 G, ψ q = 1 → q = 1 := by
    intro q hq
    obtain ⟨f, hf, hfq⟩ := hψτ q
    rw [hf, vecQ_eq_one_iff] at hq
    exact Subtype.ext (by rw [← hfq]; exact (hkerβ f).mpr hq)
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro g hg
    obtain ⟨q, x, rfl⟩ := iso_exists_mul_eq hH g
    rw [hφ] at hg
    obtain ⟨f, hf, -⟩ := hψτ q
    have hσ : sig a x = 1 := by
      refine eq_one_of_vecQ_mul_permQ f (sig a x) ?_
      rw [← hf, ← hτ]
      exact hg
    have hx1 : (x : G) = 1 :=
      Subgroup.disjoint_def.mp hH.disjoint ((sig_eq_one_iff a).mp hσ) x.2
    have hx : x = 1 := Subtype.ext hx1
    rw [hx, map_one, mul_one] at hg
    rw [hψinj q hg, hx]
    simp
  have hle : φ.range ≤ TL4.aeModel 5 := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨q, x, rfl⟩ := iso_exists_mul_eq hH g
    rw [hφ]
    refine mul_mem ?_ ?_
    · obtain ⟨f, hf, -⟩ := hψτ q
      rw [hf]
      exact vecQ_mem f
    · rw [hτ]
      exact permQ_mem (sig_mem a x)
  have hcardG : Nat.card G = 960 := by
    have h1 := h.card_pCore a
    have h2 : Nat.card (G ⧸ pCore 2 G) = 60 := by
      rw [Nat.card_congr a.toEquiv]
      exact iso_card_alternatingGroup_five
    have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (pCore 2 G)
    rw [h2, h1] at h3
    omega
  have hcardR : Nat.card φ.range = 960 := by
    rw [← hcardG]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm
  exact ⟨φ, hinj, Subgroup.eq_of_le_of_card_ge hle
    (AE5Q8.card_aeModel_five.trans hcardR.symm).le⟩

private theorem nonempty_aeIdent_of_hom {φ : G →* AE.AEQ 5} (hinj : Function.Injective φ)
    (hrange : φ.range = TL4.aeModel 5) : Nonempty (AEIdent Ω 5) := by
  have hmap : ∀ L ∈ Ω,
      (L.subgroupOf (pSpan Ω)).map (φ.comp (pSpan Ω).subtype) = L.map φ := by
    intro L hL
    rw [← Subgroup.map_map, Subgroup.map_subgroupOf_eq_of_le (le_pSpan hL)]
  have hlabel : ∀ L ∈ Ω, ∃ (α : Finset (Fin 5)) (h : α.card = 4) (b : Bool),
      L.map φ = AE.memBar α h b := by
    intro L hL
    obtain ⟨z, hz⟩ := h.exists_uniqueInvolution hL
    refine AE5Q8.eq_memBar_of_q8 (X := L.map φ) ?_ ?_ (iso_isUniqueInvolution_map hz hinj) ?_
    · rw [← hrange]
      exact Subgroup.map_le_range φ L
    · rw [Subgroup.card_map_of_injective hinj]
      exact h.card_eq hL
    · obtain ⟨x, hx, y, hy, hxy⟩ := h.nonabelian hL
      exact ⟨φ x, Subgroup.mem_map_of_mem φ hx, φ y, Subgroup.mem_map_of_mem φ hy,
        fun he => hxy (hinj (by rw [map_mul, map_mul]; exact he))⟩
  refine ⟨⟨φ.comp (pSpan Ω).subtype, ?_, ?_, ?_, ?_⟩⟩
  · have hr : (φ.comp (pSpan Ω).subtype).range = φ.range := by
      ext y
      constructor
      · rintro ⟨z, rfl⟩
        exact ⟨(z : G), rfl⟩
      · rintro ⟨g, rfl⟩
        exact ⟨⟨g, by rw [h.thmD.gen]; exact Subgroup.mem_top g⟩, rfl⟩
    rw [hr]
    exact hrange
  · have hk : (φ.comp (pSpan Ω).subtype).ker = ⊥ :=
      (MonoidHom.ker_eq_bot_iff _).mpr (hinj.comp (pSpan Ω).subtype_injective)
    rw [hk]
    exact bot_le
  · intro L hL
    rw [hmap L hL]
    exact hlabel L hL
  · intro α hα b
    obtain ⟨A, B, hp⟩ := h.exists_paired
    obtain ⟨α₀, h₀, b₀, hA⟩ := hlabel A hp.1
    obtain ⟨x, hx, hxc⟩ := AE5Q8.exists_conj_memBar_memBar α₀ h₀ b₀ α hα b
    rw [← hrange] at hx
    obtain ⟨g, rfl⟩ := hx
    have hgA : conjSub g A ∈ Ω := h.thmD.hyp.conjInvariant g A hp.1
    refine ⟨conjSub g A, hgA, ?_⟩
    rw [hmap _ hgA, iso_map_conjSub, hA, hxc]

theorem nonempty_aeIdent (a : G ⧸ pCore 2 G ≃* alternatingGroup (Fin 5)) :
    Nonempty (AEIdent Ω 5) := by
  obtain ⟨H, hH⟩ := h.exists_complement a
  obtain ⟨φ, hinj, hrange⟩ := h.exists_hom a hH
  exact h.nonempty_aeIdent_of_hom hinj hrange

end E4Hyp

end CFSG.ClassicalInvolution.Q3.Sec13
