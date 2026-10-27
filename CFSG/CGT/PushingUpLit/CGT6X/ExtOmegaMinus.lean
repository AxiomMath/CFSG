module

public import CFSG.CGT.PushingUpLit.CGT6.EmbModDefs
public import CFSG.CGT.PushingUpLit.CGT6X.ExtSplit
public import CFSG.CGT.PushingUpLit.CGT6X.ExtNatDual
public import CFSG.CGT.PushingUpLit.CGT6X.ExtNatIrr

public section

namespace CFSG.CGT.PushingUpLit.CGT6X

open CFSG.CGT.PushingUpLit.CGT6 CFSG.CGT.PushingUpLit.CGT6.TwoEight CFSG.CGT.PushingUpLit.BHS6
  CFSG.SL2MinimalFaithful

section Helpers

variable (n : ℕ) [NeZero n]

@[expose] noncomputable def eHW : Multiplicative (hermSub n) ≃* NMod n :=
  AddEquiv.toMultiplicative (minusCoord n)

theorem eHW_equivariant (A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)))
    (m : Multiplicative (hermSub n)) :
    eHW n (omegaMinusAct n A m) = rhoW n A (eHW n m) := by
  rw [omegaMinusAct_eq, rhoW_apply]
  exact (congrArg Multiplicative.ofAdd (minusHom_apply n A (Multiplicative.toAdd m))).symm

theorem dualAct_comp {H K M : Type*} [Group H] [Group K] [CommGroup M] (σ : K →* MulAut M)
    (f : H →* K) : dualAct (σ.comp f) = (dualAct σ).comp f := by
  refine MonoidHom.ext fun h => MulEquiv.ext fun φ => MonoidHom.ext fun m => ?_
  rw [dualAct_apply]
  show φ ((σ.comp f) h⁻¹ m) = (dualAct σ (f h) φ) m
  rw [dualAct_apply, MonoidHom.comp_apply, map_inv]

theorem hom_trivial_G {G : Type*} [Group G]
    (θ : G ≃* Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)))
    {X : Type*} [CommGroup X] (hX : ∀ x : X, x ^ 2 = 1) (φ : G →* X) : φ = 1 := by
  obtain ⟨w, hw⟩ := exists_sigR_ne n
  have hK : ∃ a : Fq (2 * n), a ≠ 0 ∧ a ≠ 1 := by
    refine ⟨w, ?_, ?_⟩
    · rintro rfl
      exact hw (map_zero _)
    · rintro rfl
      exact hw (map_one _)
  have h := hom_trivial_of_borel hX hK (φ.comp θ.symm.toMonoidHom)
  refine MonoidHom.ext fun g => ?_
  have := congrArg (fun f => f (θ g)) h
  simpa using this

end Helpers

section Main

theorem extOmegaMinus_holds :
    ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
      ∀ (G : Subgroup (MulAut V)) (n : ℕ), 1 ≤ n →
        (∀ A B : Subgroup V, GInv G A → GInv G B → A ⊓ B = ⊥ → A ⊔ B = ⊤ → A = ⊥ ∨ B = ⊥) →
        ∀ A B : Subgroup V, A ≤ B → GInv G A → GInv G B →
          (∀ g ∈ G, ∀ a ∈ A, g a = a) → (∀ g ∈ G, ∀ v : V, g v * v⁻¹ ∈ B) →
          IsNatSectionBy (omegaMinusAct n) G B A →
          ∀ C : Subgroup V, GInv G C → C = ⊥ ∨ C = ⊤ := by
  intro V _ _ hV G n hn hind A B hAB hAinv hBinv hAtriv hVB hnat C hC
  have : NeZero n := ⟨by omega⟩
  obtain ⟨-, θ, β, hβsurj, hβker, hβeq⟩ := hnat
  let τV : ↥G →* MulAut V := G.subtype
  have hBS : SInv τV B := fun g b hb => hBinv g g.2 b hb
  let τB : ↥G →* MulAut ↥B := resAct τV B hBS
  let AE : Subgroup ↥B := A.subgroupOf B
  let σ : ↥G →* MulAut (NMod n) := (rhoW n).comp θ.toMonoidHom
  let βn : ↥B →* NMod n := (eHW n).toMonoidHom.comp β
  have hβn_equiv : ∀ (g : ↥G) (b : ↥B), βn (τB g b) = σ g (βn b) := fun g b => by
    have := hβeq g b (hBinv g g.2 b b.2)
    show eHW n (β ⟨(g : MulAut V) b, hBinv g g.2 b b.2⟩) = rhoW n (θ g) (eHW n (β b))
    rw [this, eHW_equivariant]
  have hD : ExtData τB σ AE βn := by
    refine ⟨fun g x hx => ?_, fun g a ha => ?_, fun m => ?_, fun e => ?_, hβn_equiv⟩
    · exact hAinv g g.2 x hx
    · exact Subtype.ext (hAtriv g g.2 a ha)
    · obtain ⟨b, hb⟩ := hβsurj ((eHW n).symm m)
      exact ⟨b, by show eHW n (β b) = m; rw [hb]; exact (eHW n).apply_symm_apply m⟩
    · show eHW n (β e) = 1 ↔ e ∈ A.subgroupOf B
      rw [MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, hβker]
  have h1G : ∀ c : ↥G → NMod n, IsCocycle σ c → IsCoboundary σ c := fun c hc =>
    isCoboundary_comp (ρ := rhoW n) θ (fun c hc => h1_nat n hc) hc
  have hdualG : ∀ γ : ↥G → Dual (NMod n), IsCocycle (dualAct σ) γ →
      IsCoboundary (dualAct σ) γ := by
    intro γ hγ
    have hd : dualAct σ = (dualAct (rhoW n)).comp θ.toMonoidHom :=
      dualAct_comp (rhoW n) θ.toMonoidHom
    rw [hd] at hγ ⊢
    exact isCoboundary_comp (ρ := dualAct (rhoW n)) θ (fun c hc => h1_natDual n hc) hγ
  obtain ⟨C₁, hC₁inv, hC₁A, hC₁sup⟩ := exists_inv_complement_bottom hdualG (Nat.card AE) ↥B
    (fun x => Subtype.ext (hV x)) τB AE βn hD rfl
  let N' : Subgroup V := C₁.map B.subtype
  have hN'B : N' ≤ B := by
    rintro x ⟨c, -, rfl⟩
    exact c.2
  have hN'inv : SInv τV N' := fun g x hx => by
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx
    exact Subgroup.mem_map.2 ⟨τB g c, hC₁inv g c hc, rfl⟩
  have hN'A : N' ⊓ A = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hx1, hxA⟩
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hx1
    have h : c ∈ C₁ ⊓ AE := ⟨hc, hxA⟩
    rw [hC₁A] at h
    have h1 := Subgroup.mem_bot.1 h
    rw [h1]
    exact Subgroup.one_mem _
  have hN'sup : N' ⊔ A = B := by
    apply le_antisymm (sup_le hN'B hAB)
    intro b hb
    have h : (⟨b, hb⟩ : ↥B) ∈ C₁ ⊔ AE := by rw [hC₁sup]; exact Subgroup.mem_top _
    obtain ⟨c, hc, a, ha, hca⟩ := Subgroup.mem_sup.1 h
    exact Subgroup.mem_sup.2 ⟨(c : V), Subgroup.mem_map.2 ⟨c, hc, rfl⟩, (a : V), ha,
      congrArg Subtype.val hca⟩
  let φ0 : ↥N' →* NMod n := βn.comp (Subgroup.inclusion hN'B)
  have hφ0 : ∀ x : ↥N', φ0 x = βn ⟨x, hN'B x.2⟩ := fun x => rfl
  have hφinj : Function.Injective φ0 := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxA : (x : V) ∈ A := (hD.ker ⟨x, hN'B x.2⟩).1 hx
    have h : (x : V) ∈ N' ⊓ A := ⟨x.2, hxA⟩
    rw [hN'A] at h
    exact Subtype.ext (Subgroup.mem_bot.1 h)
  have hφsurj : Function.Surjective φ0 := by
    intro m
    obtain ⟨b, rfl⟩ := hD.surj m
    have hb : (b : V) ∈ N' ⊔ A := by rw [hN'sup]; exact b.2
    obtain ⟨x, hx, a, ha, hxa⟩ := Subgroup.mem_sup.1 hb
    refine ⟨⟨x, hx⟩, ?_⟩
    have hb' : b = ⟨x, hN'B hx⟩ * ⟨a, hAB ha⟩ := Subtype.ext hxa.symm
    rw [hφ0, hb', map_mul, (hD.ker ⟨a, hAB ha⟩).2 ha, mul_one]
  let φ : ↥N' ≃* NMod n := MulEquiv.ofBijective φ0 ⟨hφinj, hφsurj⟩
  have hφeq : ∀ (g : ↥G) (x : ↥N'), φ (resAct τV N' hN'inv g x) = σ g (φ x) := fun g x =>
    hβn_equiv g ⟨x, hN'B x.2⟩
  have hN'coh : ∀ c : ↥G → ↥N', IsCocycle (resAct τV N' hN'inv) c →
      IsCoboundary (resAct τV N' hN'inv) c := fun c hc =>
    isCoboundary_of_equiv φ.symm (fun g v => by
      apply φ.injective
      rw [hφeq, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]) h1G hc
  have hgB : ∀ (g : ↥G), ∀ b ∈ B, τV g b * b⁻¹ ∈ N' := by
    intro g b hb
    have hb' : b ∈ N' ⊔ A := by rw [hN'sup]; exact hb
    obtain ⟨x, hx, a, ha, rfl⟩ := Subgroup.mem_sup.1 hb'
    have e : τV g (x * a) * (x * a)⁻¹ = τV g x * x⁻¹ := by
      have e1 : τV g (x * a) = τV g x * a := by
        rw [map_mul]
        exact congrArg (τV g x * ·) (hAtriv g g.2 a ha)
      have e2 : τV g x * a * (x * a)⁻¹ = (τV g x * x⁻¹) * (a * a⁻¹) := by
        rw [mul_inv_rev]; ac_rfl
      rw [e1, e2, mul_inv_cancel, mul_one]
    rw [e]
    exact N'.mul_mem (hN'inv g x hx) (N'.inv_mem hx)
  let Nb : Subgroup ↥B := N'.subgroupOf B
  have hmk : ∀ (g : ↥G) (b : ↥B), (QuotientGroup.mk ⟨τV g b, hBS g b b.2⟩ : ↥B ⧸ Nb) =
      QuotientGroup.mk b := fun g b => by
    rw [QuotientGroup.eq]
    show (τV g b)⁻¹ * (b : V) ∈ N'
    have h := N'.inv_mem (hgB g b b.2)
    rw [mul_inv_rev, inv_inv, mul_comm] at h
    exact h
  let δ : ↥G → V → ↥B ⧸ Nb := fun g v => QuotientGroup.mk ⟨τV g v * v⁻¹, hVB g g.2 v⟩
  have hδmul : ∀ g h : ↥G, δ (g * h) = δ g * δ h := by
    intro g h
    funext v
    let b : ↥B := ⟨τV h v * v⁻¹, hVB h h.2 v⟩
    have e : (⟨τV (g * h) v * v⁻¹, hVB (g * h) (g * h).2 v⟩ : ↥B) =
        ⟨τV g b, hBS g b b.2⟩ * ⟨τV g v * v⁻¹, hVB g g.2 v⟩ := by
      apply Subtype.ext
      show τV (g * h) v * v⁻¹ = τV g (τV h v * v⁻¹) * (τV g v * v⁻¹)
      rw [map_mul, MulAut.mul_apply, (τV g).map_mul, (τV g).map_inv]
      have : τV g (τV h v) * (τV g v)⁻¹ * (τV g v * v⁻¹) =
          τV g (τV h v) * v⁻¹ * (τV g v * (τV g v)⁻¹) := by ac_rfl
      rw [this, mul_inv_cancel, mul_one]
    show (QuotientGroup.mk ⟨τV (g * h) v * v⁻¹, hVB (g * h) (g * h).2 v⟩ : ↥B ⧸ Nb) =
      QuotientGroup.mk ⟨τV g v * v⁻¹, hVB g g.2 v⟩ * QuotientGroup.mk ⟨τV h v * v⁻¹, hVB h h.2 v⟩
    rw [e, QuotientGroup.mk_mul, hmk g b, mul_comm]
  let hom : ↥G →* (V → ↥B ⧸ Nb) := MonoidHom.mk' δ hδmul
  have hX : ∀ f : V → ↥B ⧸ Nb, f ^ 2 = 1 := by
    intro f
    funext v
    show (f v) ^ 2 = 1
    induction f v using QuotientGroup.induction_on with
    | H b =>
      rw [← QuotientGroup.mk_pow]
      have : b ^ 2 = 1 := Subtype.ext (hV b)
      rw [this]
      rfl
  have hhom : hom = 1 := hom_trivial_G n θ hX hom
  have htriv : ∀ (g : ↥G) (v : V), τV g v * v⁻¹ ∈ N' := by
    intro g v
    have h := congrArg (fun f : ↥G →* (V → ↥B ⧸ Nb) => f g v) hhom
    have h' : (QuotientGroup.mk ⟨τV g v * v⁻¹, hVB g g.2 v⟩ : ↥B ⧸ Nb) = 1 := h
    exact (QuotientGroup.eq_one_iff (⟨τV g v * v⁻¹, hVB g g.2 v⟩ : ↥B)).1 h'
  obtain ⟨C₂, hC₂inv, hC₂N, hC₂sup⟩ := exists_inv_complement_top hV τV N' hN'inv htriv hN'coh
  have hGinv : ∀ S : Subgroup V, SInv τV S → GInv G S := fun S hS g hg a ha => hS ⟨g, hg⟩ a ha
  have hN'ne : N' ≠ ⊥ := by
    intro h0
    have hm : (Multiplicative.ofAdd ((1, 0, 0) : Wd (Fz n) (Fq (2 * n))) : NMod n) ≠ 1 := by
      intro h
      have h' := congrArg Multiplicative.toAdd h
      have h1 : (1 : Fz n) = 0 := congrArg Prod.fst h'
      exact one_ne_zero h1
    obtain ⟨x, hx⟩ := hφsurj (Multiplicative.ofAdd ((1, 0, 0) : Wd (Fz n) (Fq (2 * n))))
    have hx1 : (x : V) = 1 := (Subgroup.eq_bot_iff_forall N').1 h0 (x : V) x.2
    have hx2 : x = 1 := Subtype.ext hx1
    rw [hx2, map_one] at hx
    exact hm hx.symm
  have hN'top : N' = ⊤ := by
    rcases hind C₂ N' (hGinv _ hC₂inv) (hGinv _ hN'inv) hC₂N hC₂sup with h | h
    · rw [h, bot_sup_eq] at hC₂sup
      exact hC₂sup
    · exact absurd h hN'ne
  have hmemN' : ∀ x : V, x ∈ N' := fun x => by rw [hN'top]; exact Subgroup.mem_top x
  let ψ : V →* NMod n :=
    { toFun := fun x => φ0 ⟨x, hmemN' x⟩
      map_one' := map_one φ0
      map_mul' := fun x y => map_mul φ0 ⟨x, hmemN' x⟩ ⟨y, hmemN' y⟩ }
  have hψinj : Function.Injective ψ := fun x y h => congrArg Subtype.val (hφinj h)
  have hψeq : ∀ (g : ↥G) (x : V), ψ (τV g x) = rhoW n (θ g) (ψ x) := fun g x =>
    hφeq g ⟨x, hmemN' x⟩
  have hW : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (Fq (2 * n)), ∀ m ∈ C.map ψ,
      rhoW n A m ∈ C.map ψ := by
    intro A m hm
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.1 hm
    have hA : θ (θ.symm A) = A := θ.apply_symm_apply A
    refine Subgroup.mem_map.2 ⟨τV (θ.symm A) c, hC _ (θ.symm A).2 c hc, ?_⟩
    rw [hψeq, hA]
  rcases natModule_irreducible n (C.map ψ) hW with h | h
  · left
    rw [eq_bot_iff]
    intro c hc
    have h2 : ψ c ∈ C.map ψ := Subgroup.mem_map_of_mem ψ hc
    rw [h, Subgroup.mem_bot] at h2
    have h1 : ψ c = ψ 1 := by rw [h2, map_one]
    exact Subgroup.mem_bot.2 (hψinj h1)
  · right
    rw [eq_top_iff]
    intro v _
    have h2 : ψ v ∈ C.map ψ := by rw [h]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hcv⟩ := Subgroup.mem_map.1 h2
    rw [← hψinj hcv]
    exact hc

end Main

end CFSG.CGT.PushingUpLit.CGT6X
