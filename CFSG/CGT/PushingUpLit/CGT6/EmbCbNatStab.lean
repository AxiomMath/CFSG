module

public import CFSG.CGT.PushingUpLit.CGT6.EmbAltMod
public import CFSG.CGT.PushingUpLit.CGT6.EmbAltStab

public section

namespace CFSG.CGT.PushingUpLit.CGT6

open CFSG CFSG.Quasithin CFSG.CGT.PushingUpLit.BHS6 CFSG.CGT.PushingUp

section Helpers

variable {N : ℕ}

private abbrev cbsE (i : Fin N) : G6.PermMod N := Multiplicative.ofAdd (Pi.single i 1)

private theorem cbsE_apply (a i : Fin N) :
    Multiplicative.toAdd (cbsE a) i = (Pi.single a 1 : Fin N → ZMod 2) i := rfl

private theorem cbsE_mul_self (a : Fin N) : cbsE a * cbsE a = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  show (Pi.single a 1 : Fin N → ZMod 2) i + (Pi.single a 1 : Fin N → ZMod 2) i = 0
  exact CharTwo.add_self_eq_zero _

private theorem cbsE_mul_allOnes_mem (hN : Odd N) (a : Fin N) :
    cbsE a * G6.allOnes N ∈ G6.coreMod N := by
  rw [G6.mem_coreMod]
  simp only [toAdd_mul, Pi.add_apply, Finset.sum_add_distrib, G6.allOnes, toAdd_ofAdd]
  simp [Finset.sum_pi_single', Finset.card_univ, Fintype.card_fin]
  have h : ((N : ℕ) : ZMod 2) = 1 := ZMod.natCast_eq_one_iff_odd.mpr hN
  rw [h]
  exact CharTwo.add_self_eq_zero _

private theorem cbsE_mul_mem (a b : Fin N) : cbsE a * cbsE b ∈ G6.coreMod N := by
  rw [G6.mem_coreMod]
  simp only [toAdd_mul, Pi.add_apply, Finset.sum_add_distrib, cbsE_apply, Finset.sum_pi_single']
  simp only [Finset.mem_univ, ite_true]
  exact CharTwo.add_self_eq_zero _

private def cbsProd (p : Fin N) (T : Finset (Fin N)) : G6.PermMod N :=
  ∏ q ∈ T, (cbsE p * cbsE q)

private theorem cbsProd_coord (p : Fin N) (T : Finset (Fin N)) {i : Fin N} (hi : i ≠ p) :
    Multiplicative.toAdd (cbsProd p T) i = if i ∈ T then 1 else 0 := by
  unfold cbsProd
  rw [toAdd_prod, Finset.sum_apply]
  simp [Pi.single_apply, hi]

private theorem cbsProd_mem (p : Fin N) (T : Finset (Fin N)) : cbsProd p T ∈ G6.coreMod N :=
  Subgroup.prod_mem _ fun q _ => cbsE_mul_mem p q

private theorem cbs_eq_of_agree_off {x y : G6.PermMod N} (hx : x ∈ G6.coreMod N)
    (hy : y ∈ G6.coreMod N) (p : Fin N)
    (h : ∀ i, i ≠ p → Multiplicative.toAdd x i = Multiplicative.toAdd y i) : x = y := by
  apply Multiplicative.toAdd.injective
  funext i
  by_cases hi : i = p
  · subst hi
    rw [G6.mem_coreMod] at hx hy
    have h1 : ∑ j, (Multiplicative.toAdd x j - Multiplicative.toAdd y j) =
        Multiplicative.toAdd x i - Multiplicative.toAdd y i := by
      apply Finset.sum_eq_single i
      · intro j _ hj
        rw [h j hj, sub_self]
      · simp
    have h2 : ∑ j, (Multiplicative.toAdd x j - Multiplicative.toAdd y j) =
        ∑ j, Multiplicative.toAdd x j - ∑ j, Multiplicative.toAdd y j :=
      Finset.sum_sub_distrib (fun j => Multiplicative.toAdd x j) (fun j => Multiplicative.toAdd y j)
    rw [h2, hx, hy, sub_self] at h1
    exact (sub_eq_zero.mp h1.symm)
  · exact h i hi

private theorem cbs_eq_prod {x : G6.PermMod N} (hx : x ∈ G6.coreMod N) (F : Finset (Fin N))
    (hxF : ∀ i ∈ F, Multiplicative.toAdd x i = 0) (p : Fin N) :
    ∃ T : Finset (Fin N), (∀ q ∈ T, q ∉ F) ∧ x = cbsProd p T := by
  classical
  refine ⟨Finset.univ.filter fun q => q ∉ F ∧ q ≠ p ∧ Multiplicative.toAdd x q = 1,
    fun q hq => (Finset.mem_filter.mp hq).2.1, ?_⟩
  apply cbs_eq_of_agree_off hx (cbsProd_mem p _) p
  intro i hi
  rw [cbsProd_coord p _ hi]
  by_cases hiF : i ∈ F
  · rw [hxF i hiF]
    simp [hiF]
  · have hv : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases hv (Multiplicative.toAdd x i) with h0 | h1
    · simp [h0, hiF, hi]
    · simp [h1, hiF, hi]

end Helpers

section Restrict

variable {N : ℕ} (F : Finset (Fin N))

private noncomputable def cbsRes : G6.PermMod N →* G6.PermMod (N - F.card) where
  toFun x := Multiplicative.ofAdd fun j =>
    Multiplicative.toAdd x ((complEquiv F j : {i // i ∉ F}) : Fin N)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem cbsRes_apply (x : G6.PermMod N) (j : Fin (N - F.card)) :
    Multiplicative.toAdd (cbsRes F x) j =
      Multiplicative.toAdd x ((complEquiv F j : {i // i ∉ F}) : Fin N) := rfl

private noncomputable def cbsExt (t : G6.PermMod (N - F.card)) : G6.PermMod N :=
  Multiplicative.ofAdd fun i =>
    if h : i ∈ F then 0 else Multiplicative.toAdd t ((complEquiv F).symm ⟨i, h⟩)

private theorem cbsExt_apply_of_mem (t : G6.PermMod (N - F.card)) {i : Fin N} (hi : i ∈ F) :
    Multiplicative.toAdd (cbsExt F t) i = 0 := by
  simp [cbsExt, hi]

private theorem cbsRes_cbsExt (t : G6.PermMod (N - F.card)) : cbsRes F (cbsExt F t) = t := by
  apply Multiplicative.toAdd.injective
  funext j
  rw [cbsRes_apply]
  have h : ((complEquiv F j : {i // i ∉ F}) : Fin N) ∉ F := (complEquiv F j).2
  simp [cbsExt, h]

private theorem cbsExt_mem {t : G6.PermMod (N - F.card)} (ht : t ∈ G6.coreMod (N - F.card)) :
    cbsExt F t ∈ G6.coreMod N := by
  classical
  rw [G6.mem_coreMod] at ht ⊢
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin N => i ∉ F)]
  have h1 : ∑ i : {i : Fin N // ¬ (i ∉ F)}, Multiplicative.toAdd (cbsExt F t) i.1 = 0 :=
    Finset.sum_eq_zero fun i _ => cbsExt_apply_of_mem F t (not_not.mp i.2)
  have h2 : ∑ i : {i : Fin N // i ∉ F}, Multiplicative.toAdd (cbsExt F t) i.1 =
      ∑ j, Multiplicative.toAdd t j := by
    rw [← Equiv.sum_comp (complEquiv F)]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h : ((complEquiv F j : {i // i ∉ F}) : Fin N) ∉ F := (complEquiv F j).2
    simp [cbsExt, h]
  rw [h1, h2, ht, add_zero]

private theorem cbs_eq_one_of_res {x : G6.PermMod N} (hxF : ∀ i ∈ F, Multiplicative.toAdd x i = 0)
    (hx : cbsRes F x = 1) : x = 1 := by
  apply Multiplicative.toAdd.injective
  funext i
  by_cases hi : i ∈ F
  · exact hxF i hi
  · have h := congrArg (fun y : G6.PermMod (N - F.card) =>
      Multiplicative.toAdd y ((complEquiv F).symm ⟨i, hi⟩)) hx
    simpa [cbsRes_apply] using h

private theorem cbsRes_permAct (τ : Equiv.Perm (Fin (N - F.card))) (x : G6.PermMod N) :
    cbsRes F (G6.permAct N (Equiv.Perm.ofSubtype ((complEquiv F).permCongr τ)) x) =
      G6.permAct (N - F.card) τ (cbsRes F x) := by
  apply Multiplicative.toAdd.injective
  funext j
  simp only [cbsRes_apply, G6.permAct_apply]
  refine congrArg (Multiplicative.toAdd x) ?_
  rw [Equiv.Perm.inv_eq_iff_eq]
  have hmem : ((complEquiv F (τ⁻¹ j) : {i // i ∉ F}) : Fin N) ∉ F := (complEquiv F (τ⁻¹ j)).2
  rw [Equiv.Perm.ofSubtype_apply_of_mem (p := fun i : Fin N => i ∉ F)
    ((complEquiv F).permCongr τ) hmem]
  simp [Equiv.permCongr_apply]

private theorem cbsRes_mem {x : G6.PermMod N} (hx : x ∈ G6.coreMod N)
    (hxF : ∀ i ∈ F, Multiplicative.toAdd x i = 0) : cbsRes F x ∈ G6.coreMod (N - F.card) := by
  classical
  rw [G6.mem_coreMod] at hx ⊢
  rw [← Fintype.sum_subtype_add_sum_subtype (fun i : Fin N => i ∉ F)] at hx
  have h1 : ∑ i : {i : Fin N // ¬ (i ∉ F)}, Multiplicative.toAdd x i.1 = 0 :=
    Finset.sum_eq_zero fun i _ => hxF i.1 (not_not.mp i.2)
  rw [h1, add_zero] at hx
  rw [← hx, ← Equiv.sum_comp (complEquiv F)]
  rfl

end Restrict

section Main

variable {V : Type} [CommGroup V]

private theorem cbs_incl_equiv {N : ℕ} (F : Finset (Fin N)) (s : ↥(altStabilizer N F)) :
    altStabIncl F (altStabilizerEquiv F s) = (s : alternatingGroup (Fin N)) := by
  unfold altStabilizerEquiv
  simp only [MulEquiv.trans_apply]
  exact MonoidHom.apply_ofInjective_symm (altStabIncl_injective F) _

private theorem cbs_main {N : ℕ} (hN : Odd N) (hN5 : 5 ≤ N) {X Z : Subgroup (MulAut V)}
    (θ : X ≃* alternatingGroup (Fin N)) (hnat : IsNatSectionWith (altAct N) θ (commV X) ⊥)
    (F : Finset (Fin N)) (hm3 : 3 ≤ N - F.card) (hZX : Z ≤ X)
    (hZ : (Z.subgroupOf X).map θ.toMonoidHom = altStabilizer N F) :
    ∃ θZ : ↥Z ≃* alternatingGroup (Fin (N - F.card)),
      IsNatSectionWith (altAct (N - F.card)) θZ (commV Z) ⊥ := by
  classical
  have hsplit : commV X ⊔ fixV X = ⊤ := commV_sup_fixV_of_natural hN hN5 θ hnat
  obtain ⟨hXinv, β, hβs, hβk, hβe⟩ := hnat
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβk, Subgroup.bot_subgroupOf]
  let θ' : ↥Z ≃* ↥(altStabilizer N F) :=
    ((Subgroup.subgroupOfEquivOfLe hZX).symm.trans
      (Subgroup.equivMapOfInjective (Z.subgroupOf X) θ.toMonoidHom θ.injective)).trans
      (MulEquiv.subgroupCongr hZ)
  let θZ : ↥Z ≃* alternatingGroup (Fin (N - F.card)) := θ'.trans (altStabilizerEquiv F)
  have hθ' : ∀ z : ↥Z, ((θ' z : ↥(altStabilizer N F)) : alternatingGroup (Fin N)) =
      θ ⟨z.1, hZX z.2⟩ := fun z => rfl
  have hπ : ∀ z : ↥Z, ((θ ⟨z.1, hZX z.2⟩ : alternatingGroup (Fin N)) : Equiv.Perm (Fin N)) =
      Equiv.Perm.ofSubtype ((complEquiv F).permCongr
        ((θZ z : alternatingGroup (Fin (N - F.card))) : Equiv.Perm (Fin (N - F.card)))) := by
    intro z
    have h1 := congrArg (fun g : alternatingGroup (Fin N) => (g : Equiv.Perm (Fin N)))
      (cbs_incl_equiv F (θ' z))
    simp only [altStabIncl_apply] at h1
    rw [← hθ' z]
    exact h1.symm
  have hfixF : ∀ z : ↥Z, ∀ i ∈ F,
      ((θ ⟨z.1, hZX z.2⟩ : alternatingGroup (Fin N)) : Equiv.Perm (Fin N)) i = i := by
    intro z i hi
    rw [← hθ' z]
    exact mem_altStabilizer_iff.mp (θ' z).2 i hi
  have hS : ∀ c ∈ commV Z, ∃ hc : c ∈ commV X,
      ∀ i ∈ F, Multiplicative.toAdd ((β ⟨c, hc⟩ : ↥(G6.coreMod N)) : G6.PermMod N) i = 0 := by
    intro c hc
    induction hc using Subgroup.closure_induction with
    | mem c hc =>
      obtain ⟨z, hz, u, rfl⟩ := hc
      obtain ⟨c₀, hc₀, f, hf, hu⟩ := Subgroup.mem_sup.mp (hsplit ▸ Subgroup.mem_top u)
      have hzX : z ∈ X := hZX hz
      have hzf : z f = f := mem_fixV.mp hf z hzX
      have h1 : z u * u⁻¹ = z c₀ * c₀⁻¹ := by
        rw [← hu, map_mul, hzf]
        group
      have hzc : z c₀ ∈ commV X := hXinv z hzX c₀ hc₀
      have hmem : z u * u⁻¹ ∈ commV X := h1 ▸ (commV X).mul_mem hzc ((commV X).inv_mem hc₀)
      refine ⟨hmem, fun i hi => ?_⟩
      have hβ1 : (β ⟨z u * u⁻¹, hmem⟩ : ↥(G6.coreMod N)) =
          β ⟨z c₀, hzc⟩ * (β ⟨c₀, hc₀⟩)⁻¹ := by
        have : (⟨z u * u⁻¹, hmem⟩ : ↥(commV X)) = ⟨z c₀, hzc⟩ * ⟨c₀, hc₀⟩⁻¹ := Subtype.ext h1
        rw [this, map_mul, map_inv]
        rfl
      rw [hβ1, hβe ⟨z, hzX⟩ ⟨c₀, hc₀⟩ hzc]
      have hpi : ((θ ⟨z, hzX⟩ : alternatingGroup (Fin N)) : Equiv.Perm (Fin N))⁻¹ i = i :=
        Equiv.Perm.inv_eq_iff_eq.mpr (hfixF ⟨z, hz⟩ i hi).symm
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, altAct, G6.coreAct_coe, toAdd_mul, toAdd_inv,
        Pi.add_apply, Pi.neg_apply, G6.permAct_apply, hpi]
      exact add_neg_cancel _
    | one =>
      refine ⟨(commV X).one_mem, fun i _ => ?_⟩
      have : (⟨1, (commV X).one_mem⟩ : ↥(commV X)) = 1 := rfl
      rw [this, map_one]
      rfl
    | mul a b _ _ ha hb =>
      obtain ⟨hxa, ha'⟩ := ha
      obtain ⟨hxb, hb'⟩ := hb
      refine ⟨(commV X).mul_mem hxa hxb, fun i hi => ?_⟩
      have : (⟨a * b, (commV X).mul_mem hxa hxb⟩ : ↥(commV X)) = ⟨a, hxa⟩ * ⟨b, hxb⟩ := rfl
      rw [this, map_mul, Subgroup.coe_mul, toAdd_mul, Pi.add_apply, ha' i hi, hb' i hi, add_zero]
    | inv a _ ha =>
      obtain ⟨hxa, ha'⟩ := ha
      refine ⟨(commV X).inv_mem hxa, fun i hi => ?_⟩
      have : (⟨a⁻¹, (commV X).inv_mem hxa⟩ : ↥(commV X)) = (⟨a, hxa⟩ : ↥(commV X))⁻¹ := rfl
      rw [this, map_inv]
      show -Multiplicative.toAdd ((β ⟨a, hxa⟩ : ↥(G6.coreMod N)) : G6.PermMod N) i = 0
      rw [ha' i hi]
      exact neg_zero
  let Imc : Subgroup (G6.PermMod N) :=
    (((commV Z).subgroupOf (commV X)).map β).map (G6.coreMod N).subtype
  have hgen : ∀ p q : Fin N, p ∉ F → q ∉ F → p ≠ q → cbsE p * cbsE q ∈ Imc := by
    intro p q hpF hqF hpq
    obtain ⟨k, hkF, hkp, hkq⟩ : ∃ k : Fin N, k ∉ F ∧ k ≠ p ∧ k ≠ q := by
      by_contra hno
      have hsub : Finset.univ \ F ⊆ {p, q} := by
        intro i hi
        rw [Finset.mem_sdiff] at hi
        by_contra hne
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hne
        exact hno ⟨i, hi.2, hne.1, hne.2⟩
      have h1 := Finset.card_le_card hsub
      rw [Finset.card_univ_sdiff, Fintype.card_fin] at h1
      have h2 : ({p, q} : Finset (Fin N)).card ≤ 2 := Finset.card_le_two
      omega
    let σ : Equiv.Perm (Fin N) := Equiv.swap p q * Equiv.swap q k
    have hσp : σ p = q := by
      simp only [σ, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hpq hkp.symm, Equiv.swap_apply_left]
    have hσF : ∀ i ∈ F, σ i = i := by
      intro i hi
      have hip : i ≠ p := fun h => hpF (h ▸ hi)
      have hiq : i ≠ q := fun h => hqF (h ▸ hi)
      have hik : i ≠ k := fun h => hkF (h ▸ hi)
      simp only [σ, Equiv.Perm.mul_apply]
      rw [Equiv.swap_apply_of_ne_of_ne hiq hik, Equiv.swap_apply_of_ne_of_ne hip hiq]
    have hσalt : σ ∈ alternatingGroup (Fin N) := by
      rw [Equiv.Perm.mem_alternatingGroup]
      simp only [σ, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hpq, Equiv.Perm.sign_swap hkq.symm]
      decide
    let σ' : alternatingGroup (Fin N) := ⟨σ, hσalt⟩
    have hσ'mem : σ' ∈ altStabilizer N F := mem_altStabilizer_iff.mpr hσF
    rw [← hZ] at hσ'mem
    obtain ⟨z', hz', hz'σ⟩ := hσ'mem
    have hz'Z : (z' : MulAut V) ∈ Z := Subgroup.mem_subgroupOf.mp hz'
    obtain ⟨c₀, hc₀⟩ := hβs ⟨cbsE p * G6.allOnes N, cbsE_mul_allOnes_mem hN p⟩
    have hzc : (z' : MulAut V) (c₀ : V) ∈ commV X := hXinv _ z'.2 _ c₀.2
    let cc : ↥(commV X) := ⟨(z' : MulAut V) (c₀ : V), hzc⟩ * c₀⁻¹
    have hcc : cc ∈ (commV Z).subgroupOf (commV X) := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.subset_closure ⟨(z' : MulAut V), hz'Z, (c₀ : V), rfl⟩
    refine Subgroup.mem_map.mpr ⟨β cc, Subgroup.mem_map.mpr ⟨cc, hcc, rfl⟩, ?_⟩
    have hβcc : β cc = β ⟨(z' : MulAut V) (c₀ : V), hzc⟩ * (β c₀)⁻¹ := by
      rw [map_mul, map_inv]
      rfl
    rw [hβe z' c₀ hzc] at hβcc
    show ((β cc : ↥(G6.coreMod N)) : G6.PermMod N) = cbsE p * cbsE q
    rw [hβcc, hc₀]
    have hθz' : (θ z' : alternatingGroup (Fin N)) = σ' := hz'σ
    have hsing : ∀ i, (Pi.single p 1 : Fin N → ZMod 2) (σ⁻¹ i) =
        (Pi.single q 1 : Fin N → ZMod 2) i := by
      intro i
      simp only [Pi.single_apply, Equiv.Perm.inv_eq_iff_eq, hσp]
    have key : ∀ u v w : ZMod 2, u + w + -(v + w) = v + u := by decide
    apply Multiplicative.toAdd.injective
    funext i
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, altAct, G6.coreAct_coe, toAdd_mul, toAdd_inv,
      Pi.add_apply, Pi.neg_apply, G6.permAct_apply, hθz', G6.allOnes, toAdd_ofAdd]
    rw [show ((σ' : alternatingGroup (Fin N)) : Equiv.Perm (Fin N)) = σ from rfl, hsing i]
    exact key _ _ _
  have hresmem : ∀ c : ↥(commV Z),
      cbsRes F ((β (Subgroup.inclusion (commV_mono hZX) c) : ↥(G6.coreMod N)) : G6.PermMod N) ∈
        G6.coreMod (N - F.card) := by
    intro c
    obtain ⟨hcX, hcF⟩ := hS c.1 c.2
    exact cbsRes_mem F (β _).2 fun i hi => hcF i hi
  let f₀ : ↥(commV Z) →* G6.PermMod (N - F.card) :=
    (cbsRes F).comp (((G6.coreMod N).subtype).comp (β.comp (Subgroup.inclusion (commV_mono hZX))))
  let βZ : ↥(commV Z) →* ↥(G6.coreMod (N - F.card)) := f₀.codRestrict _ hresmem
  have hinj : Function.Injective βZ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro c hc
    rw [MonoidHom.mem_ker] at hc
    have h1 : cbsRes F ((β (Subgroup.inclusion (commV_mono hZX) c) : ↥(G6.coreMod N)) :
        G6.PermMod N) = 1 := congrArg Subtype.val hc
    obtain ⟨hcX, hcF⟩ := hS c.1 c.2
    have h2 : ((β (Subgroup.inclusion (commV_mono hZX) c) : ↥(G6.coreMod N)) : G6.PermMod N) = 1 :=
      cbs_eq_one_of_res F (fun i hi => hcF i hi) h1
    have h3 : β (Subgroup.inclusion (commV_mono hZX) c) = 1 := Subtype.ext h2
    have h4 : Subgroup.inclusion (commV_mono hZX) c = 1 := hβinj (h3.trans (map_one β).symm)
    have h5 : (c : V) = 1 := congrArg Subtype.val h4
    rw [Subgroup.mem_bot]
    exact Subtype.ext h5
  have hsurj : Function.Surjective βZ := by
    rintro ⟨t, ht⟩
    have hxmem : cbsExt F t ∈ G6.coreMod N := cbsExt_mem F ht
    have hxF : ∀ i ∈ F, Multiplicative.toAdd (cbsExt F t) i = 0 :=
      fun i hi => cbsExt_apply_of_mem F t hi
    obtain ⟨p₀, hp₀⟩ : ∃ p₀ : Fin N, p₀ ∉ F :=
      ⟨((complEquiv F ⟨0, by omega⟩ : {i // i ∉ F}) : Fin N), (complEquiv F _).2⟩
    obtain ⟨T, hTF, hxT⟩ := cbs_eq_prod hxmem F hxF p₀
    have hxImc : cbsExt F t ∈ Imc := by
      rw [hxT]
      refine Subgroup.prod_mem _ fun q hq => ?_
      by_cases hqp : q = p₀
      · subst hqp
        rw [cbsE_mul_self]
        exact Imc.one_mem
      · exact hgen p₀ q hp₀ (hTF q hq) (Ne.symm hqp)
    obtain ⟨y, hy1, hy2⟩ := Subgroup.mem_map.mp hxImc
    obtain ⟨c', hc', hc'y⟩ := Subgroup.mem_map.mp hy1
    refine ⟨⟨c'.1, Subgroup.mem_subgroupOf.mp hc'⟩, Subtype.ext ?_⟩
    show cbsRes F ((β c' : ↥(G6.coreMod N)) : G6.PermMod N) = t
    rw [hc'y]
    have hy3 : (y : G6.PermMod N) = cbsExt F t := hy2
    change cbsRes F (y : G6.PermMod N) = t
    rw [hy3, cbsRes_cbsExt]
  have hequiv : ∀ (z : ↥Z) (c : ↥(commV Z)) (hc : (z : MulAut V) c ∈ commV Z),
      βZ ⟨(z : MulAut V) c, hc⟩ = altAct (N - F.card) (θZ z) (βZ c) := by
    intro z c hc
    apply Subtype.ext
    have hzX : (z : MulAut V) ∈ X := hZX z.2
    have hcX : (c : V) ∈ commV X := commV_mono hZX c.2
    have h1 := hβe ⟨z.1, hzX⟩ ⟨c.1, hcX⟩ (hXinv _ hzX _ hcX)
    show cbsRes F ((β ⟨(z : MulAut V) c, commV_mono hZX hc⟩ : ↥(G6.coreMod N)) : G6.PermMod N) =
      G6.permAct (N - F.card) ((θZ z : alternatingGroup (Fin (N - F.card))) :
        Equiv.Perm (Fin (N - F.card))) (cbsRes F ((β ⟨c.1, hcX⟩ : ↥(G6.coreMod N)) : G6.PermMod N))
    rw [h1]
    show cbsRes F (G6.permAct N ((θ ⟨z.1, hzX⟩ : alternatingGroup (Fin N)) : Equiv.Perm (Fin N))
      ((β ⟨c.1, hcX⟩ : ↥(G6.coreMod N)) : G6.PermMod N)) = _
    rw [hπ z]
    exact cbsRes_permAct F _ _
  refine ⟨θZ, fun x hx p hp => commV_invariant hx hp, βZ, hsurj, ?_, hequiv⟩
  rw [(MonoidHom.ker_eq_bot_iff βZ).mpr hinj, Subgroup.bot_subgroupOf]

theorem natSection_stab_natural (hV : ∀ v : V, v ^ 2 = 1) {a b : ℕ} (ha : 2 ≤ a) (hb : 2 ≤ b)
    (hba : b ≤ a) {X Z : Subgroup (MulAut V)} (θ : X ≃* alternatingGroup (Fin (2 * a + 1)))
    (hnat : IsNatSectionWith (altAct (2 * a + 1)) θ (commV X) ⊥)
    (F : Finset (Fin (2 * a + 1))) (hF : F.card = (2 * a + 1) - (2 * b + 1)) (hZX : Z ≤ X)
    (hZ : (Z.subgroupOf X).map θ.toMonoidHom = altStabilizer (2 * a + 1) F) :
    ∃ θZ : ↥Z ≃* alternatingGroup (Fin (2 * b + 1)),
      IsNatSectionWith (altAct (2 * b + 1)) θZ (commV Z) ⊥ := by
  have _ := hV
  have hm : (2 * a + 1) - F.card = 2 * b + 1 := by omega
  have key : ∀ m : ℕ, m = (2 * a + 1) - F.card → ∃ θZ : ↥Z ≃* alternatingGroup (Fin m),
      IsNatSectionWith (altAct m) θZ (commV Z) ⊥ := by
    intro m hmF
    subst hmF
    exact cbs_main (odd_two_mul_add_one a) (by omega) θ hnat F (by omega) hZX hZ
  exact key (2 * b + 1) hm.symm

end Main

end CFSG.CGT.PushingUpLit.CGT6
