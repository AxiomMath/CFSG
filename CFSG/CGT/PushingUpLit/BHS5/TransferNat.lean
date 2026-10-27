module

public import CFSG.CGT.PushingUpLit.BHS5.AmbientConj

public section

namespace CFSG.CGT.PushingUpLit.BHS5

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.G6 CFSG.RankThree.PartOne CFSG.Open
  CFSG.CGT.PushingUpLit.BHS
open scoped commutatorElement

variable {Γ : Type} [Group Γ] {V : Subgroup Γ}

theorem transfer_natural (hV : IsElemAbelian 2 V) {E : Subgroup Γ}
    (hE : E ≤ Subgroup.normalizer (V : Set Γ)) {H K : Type} [Group H] [Group K]
    (act : H → K → K)
    (θ : ↥(autOn E V) ≃* H)
    (β : ↥(@commV ↥V (commGroupOfElemAbelian hV) (autOn E V)) →* K)
    (hstab : ∀ x ∈ autOn E V, ∀ p ∈ @commV ↥V (commGroupOfElemAbelian hV) (autOn E V),
      x p ∈ @commV ↥V (commGroupOfElemAbelian hV) (autOn E V))
    (hβs : Function.Surjective β)
    (hβk : β.ker = ((@commV ↥V (commGroupOfElemAbelian hV) (autOn E V)) ⊓
      @fixV ↥V (commGroupOfElemAbelian hV) (autOn E V)).subgroupOf
        (@commV ↥V (commGroupOfElemAbelian hV) (autOn E V)))
    (hβe : ∀ (x : ↥(autOn E V)) (p : ↥(@commV ↥V (commGroupOfElemAbelian hV) (autOn E V)))
      (hp : (x : MulAut ↥V) p ∈ @commV ↥V (commGroupOfElemAbelian hV) (autOn E V)),
      β ⟨(x : MulAut ↥V) p, hp⟩ = act (θ x) (β p))
    (htop : @commV ↥V (commGroupOfElemAbelian hV) (autOn E V) ⊔
      @fixV ↥V (commGroupOfElemAbelian hV) (autOn E V) = ⊤) :
    ∃ (φ : ↥E →* H) (ψ : ↥(⁅V, E⁆ : Subgroup Γ) →* K),
      Function.Surjective φ ∧
      φ.ker = (E ⊓ Subgroup.centralizer ((⁅V, E⁆ : Subgroup Γ) : Set Γ)).subgroupOf E ∧
      Function.Surjective ψ ∧
      ψ.ker = ((⁅V, E⁆ : Subgroup Γ) ⊓ Subgroup.centralizer (E : Set Γ)).subgroupOf ⁅V, E⁆ ∧
      ∀ (e : ↥E) (w : ↥(⁅V, E⁆ : Subgroup Γ))
        (hw : (e : Γ) * w * (e : Γ)⁻¹ ∈ (⁅V, E⁆ : Subgroup Γ)),
        ψ ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ = act (φ e) (ψ w) := by
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  let EF : Subgroup (MulAut ↥V) := autOn E V
  let CV : Subgroup ↥V := commV EF
  let W : Subgroup Γ := ⁅V, E⁆
  have hmap : CV.map V.subtype = W := map_commV_autOn hV hE
  have hWV : W ≤ V := hmap ▸ Subgroup.map_subtype_le _
  let ι : ↥E →* ↥EF := ((conjAct V).comp (Subgroup.inclusion hE)).codRestrict EF
    (fun e => mem_autOn_iff.2 ⟨⟨e, hE e.2⟩, e.2, rfl⟩)
  have hιapp : ∀ e : ↥E, ((ι e : ↥EF) : MulAut ↥V) = conjAct V ⟨e, hE e.2⟩ := fun e => rfl
  have hιsurj : Function.Surjective ι := fun x => by
    obtain ⟨a, haE, hax⟩ := mem_autOn_iff.1 x.2
    exact ⟨⟨a, haE⟩, Subtype.ext hax⟩
  let eW : ↥CV ≃* ↥W :=
    (Subgroup.equivMapOfInjective CV V.subtype V.subtype_injective).trans
      (MulEquiv.subgroupCongr hmap)
  have heW : ∀ q : ↥CV, ((eW q : ↥W) : Γ) = ((q : ↥V) : Γ) := fun q => rfl
  have heWs : ∀ w : ↥W, (((eW.symm w : ↥CV) : ↥V) : Γ) = (w : Γ) := fun w => by
    have := heW (eW.symm w)
    rw [MulEquiv.apply_symm_apply] at this
    exact this.symm
  refine ⟨θ.toMonoidHom.comp ι, β.comp eW.symm.toMonoidHom, θ.surjective.comp hιsurj, ?_,
    hβs.comp eW.symm.surjective, ?_, ?_⟩
  ·
    ext e
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show θ (ι e) = 1 ↔ _
    rw [← map_one θ, θ.injective.eq_iff]
    constructor
    · intro h
      have h1 : conjAct V ⟨e, hE e.2⟩ = 1 := congrArg Subtype.val h
      have hc := (conjAct_eq_one_iff V ⟨e, hE e.2⟩).1 h1
      refine ⟨e.2, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩
      exact Subgroup.mem_centralizer_iff.1 hc w (hWV hw)
    · rintro ⟨-, hc⟩
      apply Subtype.ext
      show conjAct V ⟨e, hE e.2⟩ = 1
      refine eq_one_of_trivial_on_commV htop (mem_autOn_iff.2 ⟨⟨e, hE e.2⟩, e.2, rfl⟩)
        fun p hp => ?_
      apply Subtype.ext
      rw [conjAct_apply']
      have hpW : ((p : ↥V) : Γ) ∈ W := hmap ▸ ⟨p, hp, rfl⟩
      have := Subgroup.mem_centralizer_iff.1 hc _ hpW
      calc (e : Γ) * p * (e : Γ)⁻¹ = p * (e : Γ) * (e : Γ)⁻¹ := by rw [this]
        _ = p := by group
  ·
    ext w
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    show β (eW.symm w) = 1 ↔ _
    rw [← MonoidHom.mem_ker, hβk, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, hf⟩
      refine ⟨w.2, ?_⟩
      have := (mem_fixV_autOn_iff hV hE ((eW.symm w : ↥CV) : ↥V)).1 hf
      rwa [heWs] at this
    · rintro ⟨-, hc⟩
      refine ⟨(eW.symm w).2, (mem_fixV_autOn_iff hV hE _).2 ?_⟩
      rwa [heWs]
  ·
    intro e w hw
    let p : ↥CV := eW.symm w
    have hpw : ((p : ↥V) : Γ) = (w : Γ) := heWs w
    have hmem : (ι e : MulAut ↥V) p ∈ CV := hstab _ (ι e).2 p p.2
    have hcoe : ((((ι e : MulAut ↥V) p : ↥V)) : Γ) = (e : Γ) * w * (e : Γ)⁻¹ := by
      rw [hιapp, conjAct_apply', hpw]
    have h1 : eW.symm ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩ = ⟨(ι e : MulAut ↥V) p, hmem⟩ := by
      apply eW.injective
      apply Subtype.ext
      rw [MulEquiv.apply_symm_apply]
      exact hcoe.symm
    show β (eW.symm ⟨(e : Γ) * w * (e : Γ)⁻¹, hw⟩) = act (θ (ι e)) (β (eW.symm w))
    rw [h1]
    exact hβe (ι e) p hmem

theorem isNatSL_of_slType (hV : IsElemAbelian 2 V) {E : Subgroup Γ}
    (hE : E ≤ Subgroup.normalizer (V : Set Γ)) {EF : Subgroup (MulAut ↥V)}
    (hEq : autOn E V = EF) {n : ℕ}
    (hnat : @IsSLNatSection ↥V (commGroupOfElemAbelian hV) EF
      (@commV ↥V (commGroupOfElemAbelian hV) EF)
      (@commV ↥V (commGroupOfElemAbelian hV) EF ⊓ @fixV ↥V (commGroupOfElemAbelian hV) EF) n)
    (htop : @commV ↥V (commGroupOfElemAbelian hV) EF ⊔ @fixV ↥V (commGroupOfElemAbelian hV) EF
      = ⊤) :
    IsNatSL E ⁅V, E⁆ n := by
  subst hEq
  obtain ⟨hstab, θ, β, hβs, hβk, hβe⟩ := hnat
  exact transfer_natural hV hE
    (fun (g : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 n))
      (v : Multiplicative (Fin 2 → GaloisField 2 n)) =>
      Multiplicative.ofAdd ((g : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)).mulVec
        (Multiplicative.toAdd v)))
    θ β hstab hβs hβk hβe htop

theorem isNatSym_of_symDat (hV : IsElemAbelian 2 V) {E : Subgroup Γ}
    (hE : E ≤ Subgroup.normalizer (V : Set Γ)) {EF : Subgroup (MulAut ↥V)}
    (hEq : autOn E V = EF) {m : ℕ} (D : @SymDat ↥V (commGroupOfElemAbelian hV) EF m) :
    IsNatSym E ⁅V, E⁆ m := by
  subst hEq
  let _ : CommGroup ↥V := commGroupOfElemAbelian hV
  have hc := D.commV_altOf
  have hfix : @commV ↥V (commGroupOfElemAbelian hV) (autOn E V) ⊓
      @fixV ↥V (commGroupOfElemAbelian hV) (autOn E V) = ⊥ := by
    rw [eq_bot_iff]
    intro v ⟨hvc, hvf⟩
    have := D.commV_inf_fixV_altOf
    refine (eq_bot_iff.1 this) ⟨hc ▸ hvc, fun x hx => hvf x (altOf_le D.θ hx)⟩
  exact transfer_natural hV hE (fun (σ : Equiv.Perm (Fin m)) (u : ↥(coreMod m)) => coreAct m σ u)
    D.θ D.β D.inv D.surj (by rw [hfix, Subgroup.bot_subgroupOf]; exact D.ker) D.equiv D.top

end CFSG.CGT.PushingUpLit.BHS5
