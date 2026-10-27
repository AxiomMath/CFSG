module

public import CFSG.LocalAnalysis.RankThreeUC.AGL81U4FFTorusDefs

public section

namespace CFSG.LocalAnalysis.RankThreeUC

attribute [local instance] f2Module

open CFSG.Quasithin Subgroup

variable {V : Type} [CommGroup V]

structure IsThetaFamily {c : ℕ} (Θ : Subgroup (MulAut V)) (Θi : Fin c → Subgroup (MulAut V)) :
    Prop where
  odd : Odd (Nat.card Θ)
  comm : ∀ a ∈ Θ, ∀ b ∈ Θ, a * b = b * a
  Θi_le : ∀ i, Θi i ≤ Θ
  Θi_sup : ∀ i j, i ≠ j → Θi i ⊔ Θi j = Θ

theorem IsTorusData.isThetaFamily {L : Subgroup (MulAut V)} {c : ℕ} {Θ : Subgroup (MulAut V)}
    {Θi : Fin c → Subgroup (MulAut V)} {w θ₀ : MulAut V} {π : Equiv.Perm (Fin c)}
    (h : IsTorusData L c Θ Θi w θ₀ π) : IsThetaFamily Θ Θi :=
  ⟨h.odd, h.comm, h.Θi_le, h.Θi_sup⟩

variable [Finite V]

theorem commSub_stable {Θ : Subgroup (MulAut V)} {M : Subgroup V} {g : MulAut V}
    (hgΘ : ∀ θ ∈ Θ, g * θ * g⁻¹ ∈ Θ) (hgM : ∀ w ∈ M, g w ∈ M) :
    ∀ x ∈ commSub M Θ, g x ∈ commSub M Θ := by
  intro x hx
  refine Subgroup.closure_induction (p := fun x _ => g x ∈ commSub M Θ) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨θ, hθ, w, hw, rfl⟩
    show g (θ w * w⁻¹) ∈ commSub M Θ
    have h1 : (g * θ * g⁻¹) (g w) = g (θ w) := by
      simp only [MulAut.mul_apply, MulAut.inv_apply_self]
    rw [map_mul, map_inv, ← h1]
    exact Subgroup.subset_closure ⟨g * θ * g⁻¹, hgΘ θ hθ, g w, hgM w hw, rfl⟩
  · show g 1 ∈ commSub M Θ
    rw [map_one]
    exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    show g (a * b) ∈ commSub M Θ
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    show g a⁻¹ ∈ commSub M Θ
    rw [map_inv]
    exact Subgroup.inv_mem _ ha

theorem map_commSub_le {Θ : Subgroup (MulAut V)} {M M' : Subgroup V} (f : V →* V)
    (hf : ∀ θ ∈ Θ, ∀ x, f (θ x) = θ (f x)) (hM : ∀ w ∈ M, f w ∈ M') :
    ∀ x ∈ commSub M Θ, f x ∈ commSub M' Θ := by
  intro x hx
  refine Subgroup.closure_induction (p := fun x _ => f x ∈ commSub M' Θ) ?_ ?_ ?_ ?_ hx
  · rintro _ ⟨θ, hθ, w, hw, rfl⟩
    show f (θ w * w⁻¹) ∈ commSub M' Θ
    rw [map_mul, map_inv, hf θ hθ w]
    exact Subgroup.subset_closure ⟨θ, hθ, f w, hM w hw, rfl⟩
  · show f 1 ∈ commSub M' Θ
    rw [map_one]
    exact Subgroup.one_mem _
  · intro a b _ _ ha hb
    show f (a * b) ∈ commSub M' Θ
    rw [map_mul]
    exact Subgroup.mul_mem _ ha hb
  · intro a _ ha
    show f a⁻¹ ∈ commSub M' Θ
    rw [map_inv]
    exact Subgroup.inv_mem _ ha

theorem commSub_inf_of_le [IsF2Space V] {Θ : Subgroup (MulAut V)} (hΘ : Odd (Nat.card Θ))
    {M M' : Subgroup V} (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) (hM' : ∀ g ∈ Θ, ∀ w ∈ M', g w ∈ M')
    (hle : M' ≤ M) : commSub M Θ ⊓ M' = commSub M' Θ := by
  have hV : ∀ v : V, v ^ 2 = 1 := IsF2Space.sq_eq_one
  apply le_antisymm
  · intro x hx
    obtain ⟨hxc, hxM'⟩ := Subgroup.mem_inf.mp hx
    have hdec := (coprime_decomp hΘ hV hM').1
    have hx' : x ∈ commSub M' Θ ⊔ (M' ⊓ fixV Θ) := by
      rw [hdec]
      exact hxM'
    obtain ⟨c, hc, f, hf, hcf⟩ := Subgroup.mem_sup.mp hx'
    obtain ⟨hfM', hffix⟩ := Subgroup.mem_inf.mp hf
    have hcM : c ∈ commSub M Θ := commSub_mono hle (le_refl Θ) hc
    have hfc : f ∈ commSub M Θ := by
      have hfeq : f = c⁻¹ * x := by
        rw [← hcf, inv_mul_cancel_left]
      rw [hfeq]
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hcM) hxc
    have hfM : f ∈ M := hle hfM'
    have hbot := (coprime_decomp hΘ hV hM).2
    have hf1 : f ∈ commSub M Θ ⊓ (M ⊓ fixV Θ) :=
      Subgroup.mem_inf.mpr ⟨hfc, Subgroup.mem_inf.mpr ⟨hfM, hffix⟩⟩
    rw [hbot, Subgroup.mem_bot] at hf1
    rw [← hcf, hf1, mul_one]
    exact hc
  · exact le_inf (commSub_mono hle (le_refl Θ)) (commSub_le_of_invariant hM')

theorem commSub_commSub [IsF2Space V] {Θ : Subgroup (MulAut V)} (hΘ : Odd (Nat.card Θ))
    {M : Subgroup V} (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) :
    commSub (commSub M Θ) Θ = commSub M Θ := by
  have hN : ∀ g ∈ Θ, ∀ w ∈ commSub M Θ, g w ∈ commSub M Θ := fun g hg w hw =>
    commSub_stable (g := g)
      (fun θ hθ => Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hθ) (Subgroup.inv_mem _ hg))
      (fun u hu => hM g hg u hu) w hw
  have h := commSub_inf_of_le hΘ hM hN (commSub_le_of_invariant hM)
  rw [inf_idem] at h
  exact h.symm

theorem commSub_le_commSub_of_le [IsF2Space V] {Θ : Subgroup (MulAut V)}
    (hΘ : Odd (Nat.card Θ)) {M M' : Subgroup V} (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M)
    (hM' : ∀ g ∈ Θ, ∀ w ∈ M', g w ∈ M') (h : commSub M Θ ≤ M') : commSub M Θ ≤ commSub M' Θ := by
  calc commSub M Θ = commSub (commSub M Θ) Θ := (commSub_commSub hΘ hM).symm
    _ ≤ commSub M' Θ := commSub_mono h (le_refl Θ)

theorem Rsub_inf_of_le [IsF2Space V] {Θ Θ' : Subgroup (MulAut V)} (hΘ : Odd (Nat.card Θ))
    {M M' : Subgroup V} (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) (hM' : ∀ g ∈ Θ, ∀ w ∈ M', g w ∈ M')
    (hle : M' ≤ M) : Rsub Θ Θ' M ⊓ M' = Rsub Θ Θ' M' := by
  unfold Rsub
  rw [inf_right_comm, commSub_inf_of_le hΘ hM hM' hle]

theorem Rsub_le {Θ Θ' : Subgroup (MulAut V)} {M : Subgroup V} (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) :
    Rsub Θ Θ' M ≤ M := by
  unfold Rsub
  exact inf_le_left.trans (commSub_le_of_invariant hM)

private theorem fixV_sup_RT (X Y : Subgroup (MulAut V)) : fixV (X ⊔ Y) = fixV X ⊓ fixV Y := by
  ext v
  rw [Subgroup.mem_inf]
  constructor
  · intro hv
    exact ⟨fun x hx => hv x (Subgroup.mem_sup_left hx), fun x hx => hv x (Subgroup.mem_sup_right hx)⟩
  · rintro ⟨hA, hB⟩ x hx
    rw [Subgroup.sup_eq_closure] at hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with hx | hx
      · exact hA x hx
      · exact hB x hx
    | one => rfl
    | mul x y _ _ hx hy => rw [MulAut.mul_apply, hy, hx]
    | inv x _ hx =>
      calc x⁻¹ v = x⁻¹ (x v) := by rw [hx]
        _ = v := by simp

theorem Rsub_inf_fixV_eq_bot [IsF2Space V] {Θ Θ₁ Θ₂ : Subgroup (MulAut V)}
    (hΘ : Odd (Nat.card Θ)) (hsup : Θ₁ ⊔ Θ₂ = Θ) {M : Subgroup V}
    (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) : Rsub Θ Θ₁ M ⊓ fixV Θ₂ = ⊥ := by
  have hV : ∀ v : V, v ^ 2 = 1 := IsF2Space.sq_eq_one
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨hxc, hx1f⟩ := Subgroup.mem_inf.mp hx1
  have hxfix : x ∈ fixV Θ := by
    rw [← hsup, fixV_sup_RT]
    exact Subgroup.mem_inf.mpr ⟨hx1f, hx2⟩
  have hxM : x ∈ M := commSub_le_of_invariant hM hxc
  have hbot := (coprime_decomp hΘ hV hM).2
  have hmem : x ∈ commSub M Θ ⊓ (M ⊓ fixV Θ) :=
    Subgroup.mem_inf.mpr ⟨hxc, Subgroup.mem_inf.mpr ⟨hxM, hxfix⟩⟩
  rw [hbot] at hmem
  exact hmem

theorem avgMap_of_mem_Rsub [IsF2Space V] {Θ Θ' : Subgroup (MulAut V)} (hΘ' : Odd (Nat.card Θ'))
    {M : Subgroup V} {x : V} (hx : x ∈ Rsub Θ Θ' M) : avgMap Θ' x = x :=
  avgMap_of_mem_fixV hΘ' IsF2Space.sq_eq_one (Subgroup.mem_inf.mp hx).2

theorem avgMap_commutes {Θ Θ' : Subgroup (MulAut V)} (hcomm : ∀ a ∈ Θ, ∀ b ∈ Θ, a * b = b * a)
    (hΘ' : Θ' ≤ Θ) (θ : MulAut V) (hθ : θ ∈ Θ) (x : V) :
    avgMap Θ' (θ x) = θ (avgMap Θ' x) := by
  have := Fintype.ofFinite Θ'
  rw [avgMap_apply, avgMap_apply, map_prod]
  refine Finset.prod_congr rfl fun g _ => ?_
  have hc := congrArg (fun φ : MulAut V => φ x) (hcomm _ (hΘ' g.2) θ hθ)
  simp only [MulAut.mul_apply] at hc
  exact hc

theorem avgMap_mem {Θ' : Subgroup (MulAut V)} {M : Subgroup V}
    (hM : ∀ g ∈ Θ', ∀ w ∈ M, g w ∈ M) {x : V} (hx : x ∈ M) : avgMap Θ' x ∈ M := by
  have := Fintype.ofFinite Θ'
  rw [avgMap_apply]
  exact Subgroup.prod_mem _ fun g _ => hM g g.2 x hx

theorem avgMap_mem_Rsub [IsF2Space V] {c : ℕ} {Θ : Subgroup (MulAut V)}
    {Θi : Fin c → Subgroup (MulAut V)} (hT : IsThetaFamily Θ Θi) (i : Fin c) {M : Subgroup V}
    (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) {x : V} (hx : x ∈ commSub M Θ) :
    avgMap (Θi i) x ∈ Rsub Θ (Θi i) M := by
  refine Subgroup.mem_inf.mpr ⟨?_, avgMap_mem_fixV _ x⟩
  exact map_commSub_le (avgMap (Θi i))
    (fun θ hθ y => avgMap_commutes hT.comm (hT.Θi_le i) θ hθ y)
    (fun w hw => avgMap_mem (fun g hg => hM g (hT.Θi_le i hg)) hw) x hx

private theorem odd_of_le_odd_RT {Θ Θ' : Subgroup (MulAut V)} (hΘ : Odd (Nat.card Θ))
    (h : Θ' ≤ Θ) : Odd (Nat.card Θ') :=
  Odd.of_dvd_nat hΘ (Subgroup.card_dvd_of_le h)

theorem avgMap_of_mem_Rsub_ne [IsF2Space V] {c : ℕ} {Θ : Subgroup (MulAut V)}
    {Θi : Fin c → Subgroup (MulAut V)} (hT : IsThetaFamily Θ Θi) {i j : Fin c} (hij : i ≠ j)
    {M : Subgroup V} (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) {x : V} (hx : x ∈ Rsub Θ (Θi i) M) :
    avgMap (Θi j) x = 1 := by
  have hxc : x ∈ commSub M Θ := (Subgroup.mem_inf.mp hx).1
  have hxfix : x ∈ fixV (Θi i) := (Subgroup.mem_inf.mp hx).2
  have hyc : avgMap (Θi j) x ∈ commSub M Θ :=
    map_commSub_le (avgMap (Θi j))
      (fun θ hθ y => avgMap_commutes hT.comm (hT.Θi_le j) θ hθ y)
      (fun w hw => avgMap_mem (fun g hg => hM g (hT.Θi_le j hg)) hw) x hxc
  have hyi : avgMap (Θi j) x ∈ fixV (Θi i) := by
    intro g hg
    rw [← avgMap_commutes hT.comm (hT.Θi_le j) g (hT.Θi_le i hg) x, hxfix g hg]
  have hyj : avgMap (Θi j) x ∈ fixV (Θi j) := avgMap_mem_fixV _ x
  have hmem : avgMap (Θi j) x ∈ Rsub Θ (Θi i) M ⊓ fixV (Θi j) :=
    Subgroup.mem_inf.mpr ⟨Subgroup.mem_inf.mpr ⟨hyc, hyi⟩, hyj⟩
  rw [Rsub_inf_fixV_eq_bot hT.odd (hT.Θi_sup i j hij) hM, Subgroup.mem_bot] at hmem
  exact hmem

private theorem EE_apply_eq_prod {c : ℕ} {Θi : Fin c → Subgroup (MulAut V)} (x : V) :
    EE Θi x = ∏ i, avgMap (Θi i) x := by
  unfold EE
  exact MonoidHom.finsetProd_apply _ _ _

theorem EE_idem [IsF2Space V] {c : ℕ} {Θ : Subgroup (MulAut V)}
    {Θi : Fin c → Subgroup (MulAut V)} (hT : IsThetaFamily Θ Θi) {x : V} (hx : x ∈ commV Θ) :
    EE Θi (EE Θi x) = EE Θi x := by
  rw [commV_eq_commSub] at hx
  have hM : ∀ g ∈ Θ, ∀ w ∈ (⊤ : Subgroup V), g w ∈ (⊤ : Subgroup V) :=
    fun _ _ _ _ => Subgroup.mem_top _
  have hdiag : ∀ j, avgMap (Θi j) (avgMap (Θi j) x) = avgMap (Θi j) x := fun j =>
    avgMap_of_mem_fixV (odd_of_le_odd_RT hT.odd (hT.Θi_le j)) IsF2Space.sq_eq_one
      (avgMap_mem_fixV _ x)
  have hoff : ∀ i j, i ≠ j → avgMap (Θi j) (avgMap (Θi i) x) = 1 := fun i j hij =>
    avgMap_of_mem_Rsub_ne hT hij hM (avgMap_mem_Rsub hT i hM hx)
  have hsum : ∀ j, ∏ i, avgMap (Θi j) (avgMap (Θi i) x) = avgMap (Θi j) x := fun j => by
    rw [Finset.prod_eq_single j (fun i _ hij => hoff i j hij)
      (fun h => absurd (Finset.mem_univ j) h)]
    exact hdiag j
  calc EE Θi (EE Θi x) = ∏ j, avgMap (Θi j) (∏ i, avgMap (Θi i) x) := by
        rw [EE_apply_eq_prod (Θi := Θi) (EE Θi x), EE_apply_eq_prod (Θi := Θi) x]
    _ = ∏ j, ∏ i, avgMap (Θi j) (avgMap (Θi i) x) :=
        Finset.prod_congr rfl fun j _ => map_prod (avgMap (Θi j)) _ _
    _ = ∏ j, avgMap (Θi j) x := Finset.prod_congr rfl fun j _ => hsum j
    _ = EE Θi x := (EE_apply_eq_prod (Θi := Θi) x).symm

theorem EE_mem [IsF2Space V] {c : ℕ} {Θ : Subgroup (MulAut V)}
    {Θi : Fin c → Subgroup (MulAut V)} (hT : IsThetaFamily Θ Θi) {M : Subgroup V}
    (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) {x : V} (hx : x ∈ commSub M Θ) :
    EE Θi x ∈ commSub M Θ := by
  rw [EE_apply_eq_prod]
  exact Subgroup.prod_mem _ fun i _ => (Subgroup.mem_inf.mp (avgMap_mem_Rsub hT i hM hx)).1

theorem iSupIndep_Rsub [IsF2Space V] {c : ℕ} {Θ : Subgroup (MulAut V)}
    {Θi : Fin c → Subgroup (MulAut V)} (hT : IsThetaFamily Θ Θi) {M : Subgroup V}
    (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) : iSupIndep fun i => Rsub Θ (Θi i) M := by
  rw [iSupIndep_def]
  intro i
  rw [Subgroup.disjoint_def]
  intro x hx hx'
  have hker : (⨆ j, ⨆ (_ : j ≠ i), Rsub Θ (Θi j) M) ≤ (avgMap (Θi i)).ker := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro y hy
    exact MonoidHom.mem_ker.mpr (avgMap_of_mem_Rsub_ne hT hj hM hy)
  have h1 : avgMap (Θi i) x = x :=
    avgMap_of_mem_Rsub (odd_of_le_odd_RT hT.odd (hT.Θi_le i)) hx
  have h2 : avgMap (Θi i) x = 1 := MonoidHom.mem_ker.mp (hker hx')
  rw [h1] at h2
  exact h2

theorem EE_eq_self_of_mem_iSup [IsF2Space V] {c : ℕ} {Θ : Subgroup (MulAut V)}
    {Θi : Fin c → Subgroup (MulAut V)} (hT : IsThetaFamily Θ Θi) {M : Subgroup V}
    (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) {y : V} (hy : y ∈ ⨆ i, Rsub Θ (Θi i) M) :
    EE Θi y = y := by
  refine Subgroup.iSup_induction (fun i => Rsub Θ (Θi i) M) (C := fun z => EE Θi z = z) hy ?_ ?_ ?_
  · intro i z hz
    show EE Θi z = z
    rw [EE_apply_eq_prod, Finset.prod_eq_single i]
    · exact avgMap_of_mem_Rsub (odd_of_le_odd_RT hT.odd (hT.Θi_le i)) hz
    · intro j _ hji
      exact avgMap_of_mem_Rsub_ne hT (Ne.symm hji) hM hz
    · intro h
      exact absurd (Finset.mem_univ i) h
  · show EE Θi 1 = 1
    exact map_one _
  · intro a b ha hb
    have ha' : EE Θi a = a := ha
    have hb' : EE Θi b = b := hb
    show EE Θi (a * b) = a * b
    rw [map_mul, ha', hb']

theorem iSup_Rsub_inf [IsF2Space V] {c : ℕ} {Θ : Subgroup (MulAut V)}
    {Θi : Fin c → Subgroup (MulAut V)} (hT : IsThetaFamily Θ Θi) {M Y : Subgroup V}
    (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) (hY : ∀ g ∈ Θ, ∀ w ∈ Y, g w ∈ Y) :
    (⨆ i, Rsub Θ (Θi i) M) ⊓ Y = ⨆ i, (Rsub Θ (Θi i) M ⊓ Y) := by
  have hsup : (⨆ i, Rsub Θ (Θi i) M) ≤ commSub M Θ :=
    iSup_le fun i => inf_le_left
  refine le_antisymm (fun z hz => ?_)
    (iSup_le fun i => inf_le_inf (le_iSup (fun j => Rsub Θ (Θi j) M) i) le_rfl)
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.mp hz
  have hzc : z ∈ commSub M Θ := hsup hz1
  have hEEz : EE Θi z = z := EE_eq_self_of_mem_iSup hT hM hz1
  have hcomp : ∀ i, avgMap (Θi i) z ∈ Rsub Θ (Θi i) M ⊓ Y := fun i =>
    Subgroup.mem_inf.mpr
      ⟨avgMap_mem_Rsub hT i hM hzc, avgMap_mem (fun g hg => hY g (hT.Θi_le i hg)) hz2⟩
  have hz_prod : z = ∏ i, avgMap (Θi i) z := by
    rw [← EE_apply_eq_prod (Θi := Θi) z, hEEz]
  rw [hz_prod]
  exact Subgroup.prod_mem _ fun i _ => Subgroup.mem_iSup_of_mem i (hcomp i)

theorem commSub_eq_iSup_Rsub [IsF2Space V] {c : ℕ} {Θ : Subgroup (MulAut V)}
    {Θi : Fin c → Subgroup (MulAut V)} (hT : IsThetaFamily Θ Θi) {M : Subgroup V}
    (hM : ∀ g ∈ Θ, ∀ w ∈ M, g w ∈ M) (hE : ∀ x ∈ commSub M Θ, EE Θi x = x) :
    commSub M Θ = ⨆ i, Rsub Θ (Θi i) M := by
  refine le_antisymm (fun x hx => ?_) (iSup_le fun i => inf_le_left)
  rw [← hE x hx, EE_apply_eq_prod (Θi := Θi) x]
  exact Subgroup.prod_mem _ fun i _ => Subgroup.mem_iSup_of_mem i (avgMap_mem_Rsub hT i hM hx)

private theorem Rsub_map_le {Θ Θ₁ Θ₂ : Subgroup (MulAut V)} {w : MulAut V}
    (hwΘ : ∀ θ ∈ Θ, w * θ * w⁻¹ ∈ Θ) (hwΘ' : ∀ g ∈ Θ₂, w⁻¹ * g * w ∈ Θ₁) {M : Subgroup V}
    (hwM : ∀ x ∈ M, w x ∈ M) {x : V} (hx : x ∈ Rsub Θ Θ₁ M) : w x ∈ Rsub Θ Θ₂ M := by
  obtain ⟨hxc, hxf⟩ := Subgroup.mem_inf.mp hx
  refine Subgroup.mem_inf.mpr ⟨commSub_stable hwΘ hwM x hxc, fun g hg => ?_⟩
  have h1 : (w⁻¹ * g * w) x = x := hxf _ (hwΘ' g hg)
  simp only [MulAut.mul_apply] at h1
  calc g (w x) = w (w⁻¹ (g (w x))) := (MulAut.apply_inv_self V w _).symm
    _ = w x := by rw [h1]

theorem map_Rsub {Θ Θ₁ Θ₂ : Subgroup (MulAut V)} {w : MulAut V}
    (hwΘ : ∀ θ ∈ Θ, w * θ * w⁻¹ ∈ Θ ∧ w⁻¹ * θ * w ∈ Θ)
    (hwΘ' : (∀ g ∈ Θ₁, w * g * w⁻¹ ∈ Θ₂) ∧ ∀ g ∈ Θ₂, w⁻¹ * g * w ∈ Θ₁) {M : Subgroup V}
    (hwM : ∀ x ∈ M, w x ∈ M ∧ w⁻¹ x ∈ M) :
    (Rsub Θ Θ₁ M).map (w : MulAut V).toMonoidHom = Rsub Θ Θ₂ M := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact Rsub_map_le (fun θ hθ => (hwΘ θ hθ).1) hwΘ'.2 (fun u hu => (hwM u hu).1) hx
  · intro hy
    refine ⟨w⁻¹ y, ?_, MulAut.apply_inv_self V w y⟩
    exact Rsub_map_le (w := w⁻¹) (Θ₁ := Θ₂) (Θ₂ := Θ₁)
      (fun θ hθ => by rw [inv_inv]; exact (hwΘ θ hθ).2)
      (fun g hg => by rw [inv_inv]; exact hwΘ'.1 g hg)
      (fun u hu => (hwM u hu).2) hy

theorem card_Rsub_inf_eq {Θ Θ₁ Θ₂ : Subgroup (MulAut V)} {w : MulAut V}
    (hwΘ : ∀ θ ∈ Θ, w * θ * w⁻¹ ∈ Θ ∧ w⁻¹ * θ * w ∈ Θ)
    (hwΘ' : (∀ g ∈ Θ₁, w * g * w⁻¹ ∈ Θ₂) ∧ ∀ g ∈ Θ₂, w⁻¹ * g * w ∈ Θ₁) {M Y : Subgroup V}
    (hwM : ∀ x ∈ M, w x ∈ M ∧ w⁻¹ x ∈ M) (hwY : ∀ x ∈ Y, w x ∈ Y ∧ w⁻¹ x ∈ Y) :
    Nat.card ↥(Rsub Θ Θ₂ M ⊓ Y) = Nat.card ↥(Rsub Θ Θ₁ M ⊓ Y) := by
  have hinj : Function.Injective (w : MulAut V).toMonoidHom := w.injective
  have hY : Y.map (w : MulAut V).toMonoidHom = Y := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact (hwY x hx).1
    · intro hy
      exact ⟨w⁻¹ y, (hwY y hy).2, MulAut.apply_inv_self V w y⟩
  have hmap : (Rsub Θ Θ₁ M ⊓ Y).map (w : MulAut V).toMonoidHom = Rsub Θ Θ₂ M ⊓ Y := by
    rw [Subgroup.map_inf _ _ _ hinj, map_Rsub hwΘ hwΘ' hwM, hY]
  rw [← hmap, Subgroup.card_map_of_injective hinj]

theorem card_Rsub_eq {Θ Θ₁ Θ₂ : Subgroup (MulAut V)} {w : MulAut V}
    (hwΘ : ∀ θ ∈ Θ, w * θ * w⁻¹ ∈ Θ ∧ w⁻¹ * θ * w ∈ Θ)
    (hwΘ' : (∀ g ∈ Θ₁, w * g * w⁻¹ ∈ Θ₂) ∧ ∀ g ∈ Θ₂, w⁻¹ * g * w ∈ Θ₁) {M : Subgroup V}
    (hwM : ∀ x ∈ M, w x ∈ M ∧ w⁻¹ x ∈ M) :
    Nat.card ↥(Rsub Θ Θ₂ M) = Nat.card ↥(Rsub Θ Θ₁ M) := by
  have hinj : Function.Injective (w : MulAut V).toMonoidHom := w.injective
  rw [← map_Rsub hwΘ hwΘ' hwM, Subgroup.card_map_of_injective hinj]

theorem Rsub_le_of_le {Θ Θ₁ Θ₂ : Subgroup (MulAut V)} {w : MulAut V}
    (hwΘ : ∀ θ ∈ Θ, w * θ * w⁻¹ ∈ Θ ∧ w⁻¹ * θ * w ∈ Θ)
    (hwΘ' : (∀ g ∈ Θ₁, w * g * w⁻¹ ∈ Θ₂) ∧ ∀ g ∈ Θ₂, w⁻¹ * g * w ∈ Θ₁) {M Y : Subgroup V}
    (hwM : ∀ x ∈ M, w x ∈ M ∧ w⁻¹ x ∈ M) (hwY : ∀ x ∈ Y, w x ∈ Y ∧ w⁻¹ x ∈ Y)
    (h : Rsub Θ Θ₁ M ≤ Y) : Rsub Θ Θ₂ M ≤ Y := by
  intro y hy
  rw [← map_Rsub hwΘ hwΘ' hwM, Subgroup.mem_map] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  exact (hwY x (h hx)).1

end CFSG.LocalAnalysis.RankThreeUC
