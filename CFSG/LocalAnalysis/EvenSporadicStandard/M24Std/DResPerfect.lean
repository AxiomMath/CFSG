module

public import CFSG.LocalAnalysis.EvenSporadicStandard.M24Std.DResSwap

public section

namespace CFSG.EvenSporadicStandard.M24Std.DRes

open Subgroup CFSG.Open
open scoped commutatorElement

section LayerHyp

variable {Y : Type} [Group Y] [Finite Y] {t : Y} {H : Subgroup Y}

omit [Finite Y] in
theorem LayerHyp.mul_self (hY : LayerHyp t H) : t * t = 1 := by
  have := pow_orderOf_eq_one t
  rwa [hY.order, sq] at this

theorem LayerHyp.eq_one_of_mem_oddCore (hY : LayerHyp t H) {y : Y}
    (hy : y ∈ fusionOddCore Y) (hc : t * y = y * t) : y = 1 := by
  obtain ⟨hs, hnab⟩ := hY.simple
  obtain ⟨hHq, hZ⟩ := isQuasisimple_center_eq_bot_of_isSimpleGroup hnab
  have hdisj := disjoint_fusionOddCore hHq hZ
  have hyC : y ∈ H ⊔ zpowers t := hY.cent ▸ mem_centralizer_singleton_iff.2 hc.symm
  have hle : zpowers t ≤ normalizer (H : Set Y) :=
    zpowers_le.2 (centralizer_le_normalizer _ hY.comm)
  have hset := coe_mul_of_right_le_normalizer_left H (zpowers t) hle
  have hy' : y ∈ ((H ⊔ zpowers t : Subgroup Y) : Set Y) := hyC
  rw [hset] at hy'
  obtain ⟨h, hh, w, hw, rfl⟩ := Set.mem_mul.1 hy'
  rcases eq_one_or_eq_of_mem_zpowers hY.order hw with hw1 | hwt
  · rw [hw1, mul_one] at hy ⊢
    exact (disjoint_def.1 hdisj) hh hy
  · rw [hwt] at hy
    exfalso
    have hth : t * h = h * t := (mem_centralizer_iff.1 hY.comm h hh).symm
    have hsq : (h * t) * (h * t) = h * h := by
      calc (h * t) * (h * t) = h * (t * h) * t := by group
        _ = h * (h * t) * t := by rw [hth]
        _ = h * h * (t * t) := by group
        _ = h * h := by rw [hY.mul_self, mul_one]
    have hsqO : h * h ∈ fusionOddCore Y := hsq ▸ mul_mem hy hy
    have hh1 : h * h = 1 := (disjoint_def.1 hdisj) (mul_mem hh hh) hsqO
    have hyy : (h * t) * (h * t) = 1 := hsq.trans hh1
    have hord : orderOf (h * t) ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [sq]; exact hyy)
    have hodd : Odd (orderOf (h * t)) :=
      Odd.of_dvd_nat (odd_natCard_fusionOddCore Y) (Subgroup.orderOf_dvd_natCard _ hy)
    have h1 : h * t = 1 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hord with h2 | h2
      · exact orderOf_eq_one_iff.1 h2
      · rw [h2] at hodd
        exact absurd hodd (by decide)
    have htH : t ∈ H := by
      have : t = h⁻¹ := by
        calc t = h⁻¹ * (h * t) := by group
          _ = h⁻¹ := by rw [h1, mul_one]
      rw [this]
      exact inv_mem hh
    have htc : (⟨t, htH⟩ : H) ∈ center H := by
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (mem_centralizer_iff.1 hY.comm g g.2)
    rw [hZ, mem_bot] at htc
    have ht1 : t = 1 := congrArg Subtype.val htc
    have h2 := hY.order
    rw [ht1, orderOf_one] at h2
    exact absurd h2 (by norm_num)

theorem LayerHyp.inv_of_mem_oddCore (hY : LayerHyp t H) :
    (∀ w ∈ fusionOddCore Y, t * w * t⁻¹ = w⁻¹) ∧
      ∀ w ∈ fusionOddCore Y, ∀ w' ∈ fusionOddCore Y, w * w' = w' * w := by
  have hfpf : MonoidHom.FixedPointFree (MulAut.conjNormal (H := fusionOddCore Y) t) := by
    intro g hg
    have hg' : t * (g : Y) * t⁻¹ = g := congrArg Subtype.val hg
    have : t * (g : Y) = (g : Y) * t := by
      calc t * (g : Y) = (t * (g : Y) * t⁻¹) * t := by group
        _ = (g : Y) * t := by rw [hg']
    exact Subtype.ext (hY.eq_one_of_mem_oddCore g.2 this)
  have hinv : Function.Involutive (MulAut.conjNormal (H := fusionOddCore Y) t) := by
    intro g
    apply Subtype.ext
    show t * (t * (g : Y) * t⁻¹) * t⁻¹ = g
    have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right hY.mul_self
    rw [hti]
    calc t * (t * (g : Y) * t) * t = (t * t) * (g : Y) * (t * t) := by group
      _ = g := by rw [hY.mul_self]; group
  refine ⟨fun w hw => ?_, fun w hw w' hw' => ?_⟩
  · have := congrFun (hfpf.coe_eq_inv_of_involutive hinv) ⟨w, hw⟩
    exact congrArg Subtype.val this
  · exact congrArg Subtype.val (hfpf.commute_all_of_involutive hinv ⟨w, hw⟩ ⟨w', hw'⟩)

@[expose] def pClosure (H : Subgroup Y) : Subgroup Y := Subgroup.normalClosure (H : Set Y)

instance pClosure_normal (H : Subgroup Y) : (pClosure H).Normal :=
  Subgroup.normalClosure_normal

omit [Finite Y] in
theorem le_pClosure (H : Subgroup Y) : H ≤ pClosure H := Subgroup.subset_normalClosure

omit [Finite Y] in
theorem LayerHyp.commutator_self (hY : LayerHyp t H) : ⁅H, H⁆ = H := by
  obtain ⟨eH⟩ := hY.iso
  have : Group.IsPerfect (alternatingGroup (Fin 8)) := ⟨alt8_commutator⟩
  have : Group.IsPerfect H :=
    Group.IsPerfect.ofSurjective (f := eH.symm.toMonoidHom) eH.symm.surjective
  exact Subgroup.isPerfect_iff.1 this

omit [Finite Y] in
theorem LayerHyp.pClosure_perfect (hY : LayerHyp t H) : ⁅pClosure H, pClosure H⁆ = pClosure H := by
  refine le_antisymm (commutator_le_self _) ?_
  refine Subgroup.normalClosure_le_normal ?_
  intro x hx
  have := commutator_mono (le_pClosure H) (le_pClosure H)
  rw [hY.commutator_self] at this
  exact this hx

theorem LayerHyp.proj_mem_of_mem_pClosure (hY : LayerHyp t H)
    (hc : Nat.card (egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) :
      Subgroup (Yb Y)) = 20160) {x : Y} (hx : x ∈ pClosure H) : proj Y x ∈ egaLayer (Yb Y) := by
  have hHE : H.map (proj Y) ≤ egaLayer (Yb Y) := by
    rw [hY.map_eq hc]; exact inf_le_left
  have : pClosure H ≤ (egaLayer (Yb Y)).comap (proj Y) := by
    refine Subgroup.normalClosure_le_normal ?_
    intro h hh
    exact hHE ⟨h, hh, rfl⟩
  exact this hx

theorem LayerHyp.exists_mem_pClosure (hY : LayerHyp t H)
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 8) × alternatingGroup (Fin 8))
    {f₁ f₂ : MulAut (alternatingGroup (Fin 8))} (hsw : IsSwap t e f₁ f₂)
    (hc : Nat.card (egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) :
      Subgroup (Yb Y)) = 20160) (g : egaLayer (Yb Y)) :
    ∃ x ∈ pClosure H, proj Y x = g := by
  have hPn : ((pClosure H).map (proj Y)).Normal :=
    Subgroup.Normal.map inferInstance (proj Y) (QuotientGroup.mk'_surjective _)
  let K' : Subgroup (egaLayer (Yb Y)) :=
    ((pClosure H).map (proj Y)).comap (egaLayer (Yb Y)).subtype
  have hK'n : K'.Normal := Subgroup.Normal.comap hPn _
  let M : Subgroup (alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) :=
    K'.map e.toMonoidHom
  have hMn : M.Normal := Subgroup.Normal.map hK'n e.toMonoidHom e.surjective
  obtain ⟨b, hb⟩ := alt8_nontrivial
  obtain ⟨h, hh, hhE, hhe⟩ := hY.exists_diag e hsw hc b
  have hf1 : f₁ b ≠ 1 := by
    intro h1
    apply hb
    rw [← hsw.inv b, h1, map_one]
  have hm : (f₁ b, b) ∈ M := by
    refine ⟨⟨proj Y h, hhE⟩, ?_, hhe⟩
    exact ⟨h, le_pClosure H hh, rfl⟩
  have htop : M = ⊤ := prod_normal_eq_top M hf1 hb hm
  have hg : e g ∈ M := by rw [htop]; trivial
  obtain ⟨k, hk, hke⟩ := hg
  have hkg : k = g := e.injective hke
  rw [hkg] at hk
  exact hk

theorem LayerHyp.pClosure_central (hY : LayerHyp t H)
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 8) × alternatingGroup (Fin 8))
    {f₁ f₂ : MulAut (alternatingGroup (Fin 8))} (hsw : IsSwap t e f₁ f₂)
    (hc : Nat.card (egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) :
      Subgroup (Yb Y)) = 20160) {x w : Y} (hx : x ∈ pClosure H) (hw : w ∈ fusionOddCore Y)
    (hwP : w ∈ pClosure H) : x * w = w * x := by
  obtain ⟨hinv, hcomm⟩ := hY.inv_of_mem_oddCore
  have hti : t⁻¹ = t := inv_eq_of_mul_eq_one_right hY.mul_self
  let W : Subgroup Y := pClosure H ⊓ fusionOddCore Y
  let KW : Subgroup Y := pClosure H ⊓ centralizer (W : Set Y)
  have hWn : ∀ g ∈ pClosure H, ∀ v ∈ W, g * v * g⁻¹ ∈ W := fun g hg v hv =>
    mem_inf.2 ⟨(pClosure_normal H).conj_mem v (mem_inf.1 hv).1 g,
      (inferInstance : (fusionOddCore Y).Normal).conj_mem v (mem_inf.1 hv).2 g⟩
  have hKWn : ∀ g ∈ pClosure H, ∀ k ∈ KW, g * k * g⁻¹ ∈ KW := by
    intro g hg k hk
    refine mem_inf.2 ⟨(pClosure_normal H).conj_mem k (mem_inf.1 hk).1 g, ?_⟩
    rw [mem_centralizer_iff]
    intro v hv
    have hv' : g⁻¹ * v * g ∈ W := by
      have := hWn g⁻¹ (inv_mem hg) v hv
      simpa using this
    have hkc := mem_centralizer_iff.1 (mem_inf.1 hk).2 _ hv'
    calc v * (g * k * g⁻¹) = g * ((g⁻¹ * v * g) * k) * g⁻¹ := by group
      _ = g * (k * (g⁻¹ * v * g)) * g⁻¹ := by rw [hkc]
      _ = g * k * g⁻¹ * v := by group
  let M0 : Subgroup (egaLayer (Yb Y)) := (KW.map (proj Y)).comap (egaLayer (Yb Y)).subtype
  have hM0n : M0.Normal := by
    refine ⟨fun k hk g => ?_⟩
    obtain ⟨x1, hx1, hx1g⟩ := hY.exists_mem_pClosure e hsw hc g
    obtain ⟨κ, hκ, hκk⟩ := hk
    show ((g * k * g⁻¹ : egaLayer (Yb Y)) : Yb Y) ∈ KW.map (proj Y)
    refine ⟨x1 * κ * x1⁻¹, hKWn x1 hx1 κ hκ, ?_⟩
    simp only [map_mul, map_inv, hx1g, hκk]
    rfl
  let M : Subgroup (alternatingGroup (Fin 8) × alternatingGroup (Fin 8)) := M0.map e.toMonoidHom
  have hMn : M.Normal := Subgroup.Normal.map hM0n e.toMonoidHom e.surjective
  obtain ⟨a, ha⟩ := alt8_nontrivial
  obtain ⟨x0, hx0, hx0e⟩ := hY.exists_mem_pClosure e hsw hc (e.symm (a, 1))
  have hκP : x0⁻¹ * t * x0 * t⁻¹ ∈ pClosure H := by
    have h1 : x0⁻¹ * t * x0 * t⁻¹ = x0⁻¹ * (t * x0 * t⁻¹) := by group
    rw [h1]
    exact mul_mem (inv_mem hx0) ((pClosure_normal H).conj_mem x0 hx0 t)
  have hκKW : x0⁻¹ * t * x0 * t⁻¹ ∈ KW := by
    refine mem_inf.2 ⟨hκP, mem_centralizer_iff.2 fun v hv => ?_⟩
    have hvO : v ∈ fusionOddCore Y := (mem_inf.1 hv).2
    have h1 : t⁻¹ * v * t = v⁻¹ := by
      have h := hinv v hvO
      rw [hti] at h ⊢
      exact h
    have hu : x0 * v⁻¹ * x0⁻¹ ∈ fusionOddCore Y :=
      (inferInstance : (fusionOddCore Y).Normal).conj_mem _ (inv_mem hvO) x0
    have key : (x0⁻¹ * t * x0 * t⁻¹) * v * (x0⁻¹ * t * x0 * t⁻¹)⁻¹ = v := by
      calc (x0⁻¹ * t * x0 * t⁻¹) * v * (x0⁻¹ * t * x0 * t⁻¹)⁻¹
          = x0⁻¹ * (t * (x0 * (t⁻¹ * v * t) * x0⁻¹) * t⁻¹) * x0 := by group
        _ = x0⁻¹ * (t * (x0 * v⁻¹ * x0⁻¹) * t⁻¹) * x0 := by rw [h1]
        _ = x0⁻¹ * (x0 * v⁻¹ * x0⁻¹)⁻¹ * x0 := by rw [hinv _ hu]
        _ = v := by group
    calc v * (x0⁻¹ * t * x0 * t⁻¹)
        = ((x0⁻¹ * t * x0 * t⁻¹) * v * (x0⁻¹ * t * x0 * t⁻¹)⁻¹) * (x0⁻¹ * t * x0 * t⁻¹) := by
          rw [key]
      _ = (x0⁻¹ * t * x0 * t⁻¹) * v := by group
  have hκM : (a⁻¹, f₂ a) ∈ M := by
    have hκE : proj Y (x0⁻¹ * t * x0 * t⁻¹) ∈ egaLayer (Yb Y) :=
      hY.proj_mem_of_mem_pClosure hc hκP
    refine ⟨⟨proj Y (x0⁻¹ * t * x0 * t⁻¹), hκE⟩, ⟨_, hκKW, rfl⟩, ?_⟩
    have hgt := hsw.conj (e.symm (a, 1))
    rw [MulEquiv.apply_symm_apply] at hgt
    simp only [map_one] at hgt
    have heq : (⟨proj Y (x0⁻¹ * t * x0 * t⁻¹), hκE⟩ : egaLayer (Yb Y)) =
        (e.symm (a, 1))⁻¹ * ⟨proj Y t * (e.symm (a, 1) : Yb Y) * (proj Y t)⁻¹,
          (egaLayer_normal _).conj_mem _ (e.symm (a, 1)).2 _⟩ := by
      apply Subtype.ext
      simp only [map_mul, map_inv, hx0e, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    show e (⟨proj Y (x0⁻¹ * t * x0 * t⁻¹), hκE⟩ : egaLayer (Yb Y)) = (a⁻¹, f₂ a)
    rw [heq, map_mul, map_inv, MulEquiv.apply_symm_apply, hgt]
    ext <;> simp
  have hf2a : f₂ a ≠ 1 := fun h => ha (f₂.injective (h.trans (map_one f₂).symm))
  have hMtop : M = ⊤ := prod_normal_eq_top M (inv_ne_one.2 ha) hf2a hκM
  have hxKW : x ∈ KW := by
    have hxE := hY.proj_mem_of_mem_pClosure hc hx
    have hg : e ⟨proj Y x, hxE⟩ ∈ M := by rw [hMtop]; trivial
    obtain ⟨k0, hk0, hk0e⟩ := hg
    have hk0g : k0 = ⟨proj Y x, hxE⟩ := e.injective hk0e
    rw [hk0g] at hk0
    obtain ⟨k, hk, hkx⟩ := hk0
    have hkxP : k⁻¹ * x ∈ pClosure H := mul_mem (inv_mem (mem_inf.1 hk).1) hx
    have hkxO : k⁻¹ * x ∈ fusionOddCore Y := by
      apply (QuotientGroup.eq_one_iff _).1
      show proj Y (k⁻¹ * x) = 1
      have hkx' : proj Y k = proj Y x := hkx
      rw [map_mul, map_inv, hkx']
      group
    have hWK : k⁻¹ * x ∈ KW := by
      refine mem_inf.2 ⟨hkxP, mem_centralizer_iff.2 fun v hv => ?_⟩
      exact hcomm v (mem_inf.1 hv).2 _ hkxO
    have : x = k * (k⁻¹ * x) := by group
    rw [this]
    exact mul_mem hk hWK
  exact (mem_centralizer_iff.1 (mem_inf.1 hxKW).2 w (mem_inf.2 ⟨hwP, hw⟩)).symm

@[expose] noncomputable def LayerHyp.pToProd (hY : LayerHyp t H)
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 8) × alternatingGroup (Fin 8))
    (hc : Nat.card (egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) :
      Subgroup (Yb Y)) = 20160) :
    ↥(pClosure H) →* alternatingGroup (Fin 8) × alternatingGroup (Fin 8) :=
  e.toMonoidHom.comp (((proj Y).comp (pClosure H).subtype).codRestrict (egaLayer (Yb Y))
    (fun x => hY.proj_mem_of_mem_pClosure hc x.2))

theorem LayerHyp.pToProd_apply (hY : LayerHyp t H)
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 8) × alternatingGroup (Fin 8))
    (hc : Nat.card (egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) :
      Subgroup (Yb Y)) = 20160) (x : ↥(pClosure H)) :
    hY.pToProd e hc x = e ⟨proj Y x.1, hY.proj_mem_of_mem_pClosure hc x.2⟩ := rfl

theorem LayerHyp.pClosure_inf_oddCore (hY : LayerHyp t H)
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 8) × alternatingGroup (Fin 8))
    {f₁ f₂ : MulAut (alternatingGroup (Fin 8))} (hsw : IsSwap t e f₁ f₂)
    (hc : Nat.card (egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) :
      Subgroup (Yb Y)) = 20160) {x : Y} (hx : x ∈ pClosure H) (hxO : x ∈ fusionOddCore Y) :
    x = 1 := by
  have hperf : commutator ↥(pClosure H) = ⊤ := by
    have : Group.IsPerfect ↥(pClosure H) := Subgroup.isPerfect_iff.2 hY.pClosure_perfect
    exact Group.IsPerfect.commutator_eq_top
  have hsurj : Function.Surjective (hY.pToProd e hc) := by
    intro p
    obtain ⟨x, hx, hxg⟩ := hY.exists_mem_pClosure e hsw hc (e.symm p)
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hY.pToProd_apply]
    have : (⟨proj Y x, hY.proj_mem_of_mem_pClosure hc hx⟩ : egaLayer (Yb Y)) = e.symm p :=
      Subtype.ext hxg
    rw [this, MulEquiv.apply_symm_apply]
  have hmemker : ∀ y : ↥(pClosure H), y ∈ (hY.pToProd e hc).ker ↔ y.1 ∈ fusionOddCore Y := by
    intro y
    rw [MonoidHom.mem_ker, hY.pToProd_apply]
    constructor
    · intro h
      have h1 : (⟨proj Y y.1, hY.proj_mem_of_mem_pClosure hc y.2⟩ : egaLayer (Yb Y)) = 1 :=
        e.injective (h.trans (map_one e).symm)
      exact (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val h1)
    · intro h
      have h1 : (⟨proj Y y.1, hY.proj_mem_of_mem_pClosure hc y.2⟩ : egaLayer (Yb Y)) = 1 :=
        Subtype.ext ((QuotientGroup.eq_one_iff _).2 h)
      rw [h1, map_one]
  have hker : (hY.pToProd e hc).ker ≤ center ↥(pClosure H) := by
    intro y hy
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (hY.pClosure_central e hsw hc g.2 ((hmemker y).1 hy) y.2)
  have hodd : Odd (Nat.card (hY.pToProd e hc).ker) := by
    have hle : (hY.pToProd e hc).ker.map (pClosure H).subtype ≤ fusionOddCore Y := by
      rintro _ ⟨y, hy, rfl⟩
      exact (hmemker y).1 hy
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (pClosure H).subtype_injective] at h1
    exact Odd.of_dvd_nat (odd_natCard_fusionOddCore Y) h1
  have hbot := DRes.ker_eq_bot_of_perfect_central_alt8_prod hperf (hY.pToProd e hc) hsurj hker hodd
  have : (⟨x, hx⟩ : ↥(pClosure H)) ∈ (hY.pToProd e hc).ker := (hmemker _).2 hxO
  rw [hbot, Subgroup.mem_bot] at this
  exact congrArg Subtype.val this

theorem LayerHyp.pToProd_conj (hY : LayerHyp t H)
    (e : egaLayer (Yb Y) ≃* alternatingGroup (Fin 8) × alternatingGroup (Fin 8))
    {f₁ f₂ : MulAut (alternatingGroup (Fin 8))} (hsw : IsSwap t e f₁ f₂)
    (hc : Nat.card (egaLayer (Yb Y) ⊓ centralizer ({proj Y t} : Set (Yb Y)) :
      Subgroup (Yb Y)) = 20160) (x : ↥(pClosure H)) :
    hY.pToProd e hc ⟨t * x.1 * t⁻¹, (pClosure_normal H).conj_mem _ x.2 _⟩ =
      (f₁ (hY.pToProd e hc x).2, f₂ (hY.pToProd e hc x).1) := by
  rw [hY.pToProd_apply, hY.pToProd_apply]
  have h := hsw.conj ⟨proj Y x.1, hY.proj_mem_of_mem_pClosure hc x.2⟩
  rw [← h]
  congr 1

theorem LayerHyp.exists_factors (hY : LayerHyp t H)
    (hE : Nonempty (egaLayer (Yb Y) ≃* alternatingGroup (Fin 8) × alternatingGroup (Fin 8))) :
    ∃ S1 S2 : Subgroup Y, Nonempty (S1 ≃* alternatingGroup (Fin 8)) ∧
      Nonempty (S2 ≃* alternatingGroup (Fin 8)) ∧
      (∀ a ∈ S1, ∀ b ∈ S2, a * b = b * a) ∧ Disjoint S1 S2 ∧
      Disjoint S1 (fusionOddCore Y) ∧ Disjoint S2 (fusionOddCore Y) ∧
      (∀ g ∈ S1, t * g * t⁻¹ ∈ S2) ∧ (∀ g ∈ S2, t * g * t⁻¹ ∈ S1) ∧
      (∀ h ∈ H, ∃ a ∈ S1, ∃ b ∈ S2, h = a * b) := by
  obtain ⟨e⟩ := hE
  obtain ⟨f₁, f₂, hsw, hc⟩ := hY.swap e
  set f := hY.pToProd e hc with hf
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : (⟨proj Y x.1, hY.proj_mem_of_mem_pClosure hc x.2⟩ : egaLayer (Yb Y)) = 1 :=
      e.injective (by rw [← hY.pToProd_apply e hc x, hx, map_one])
    have hxO : x.1 ∈ fusionOddCore Y := (QuotientGroup.eq_one_iff _).1 (congrArg Subtype.val h1)
    exact Subtype.ext (hY.pClosure_inf_oddCore e hsw hc x.2 hxO)
  have hsurj : Function.Surjective f := by
    intro p
    obtain ⟨x, hx, hxg⟩ := hY.exists_mem_pClosure e hsw hc (e.symm p)
    refine ⟨⟨x, hx⟩, ?_⟩
    rw [hY.pToProd_apply]
    have : (⟨proj Y x, hY.proj_mem_of_mem_pClosure hc hx⟩ : egaLayer (Yb Y)) = e.symm p :=
      Subtype.ext hxg
    rw [this, MulEquiv.apply_symm_apply]
  let F : ↥(pClosure H) ≃* alternatingGroup (Fin 8) × alternatingGroup (Fin 8) :=
    MulEquiv.ofBijective f ⟨hinj, hsurj⟩
  have hFf : ∀ x, F x = f x := fun x => rfl
  let ι₁ : alternatingGroup (Fin 8) →* Y :=
    (pClosure H).subtype.comp (F.symm.toMonoidHom.comp (MonoidHom.inl _ _))
  let ι₂ : alternatingGroup (Fin 8) →* Y :=
    (pClosure H).subtype.comp (F.symm.toMonoidHom.comp (MonoidHom.inr _ _))
  have hι₁ : Function.Injective ι₁ := by
    intro a b h
    have h1 : F.symm (a, 1) = F.symm (b, 1) := Subtype.ext h
    have := F.symm.injective h1
    exact (Prod.ext_iff.1 this).1
  have hι₂ : Function.Injective ι₂ := by
    intro a b h
    have h1 : F.symm (1, a) = F.symm (1, b) := Subtype.ext h
    have := F.symm.injective h1
    exact (Prod.ext_iff.1 this).2
  have hι₁P : ∀ a, ι₁ a ∈ pClosure H := fun a => (F.symm (a, 1)).2
  have hι₂P : ∀ a, ι₂ a ∈ pClosure H := fun a => (F.symm (1, a)).2
  have hι₁F : ∀ a, f ⟨ι₁ a, hι₁P a⟩ = (a, 1) := fun a => by
    show F ⟨ι₁ a, hι₁P a⟩ = (a, 1)
    rw [← F.apply_symm_apply (a, 1)]
    rfl
  have hι₂F : ∀ a, f ⟨ι₂ a, hι₂P a⟩ = (1, a) := fun a => by
    show F ⟨ι₂ a, hι₂P a⟩ = (1, a)
    rw [← F.apply_symm_apply (1, a)]
    rfl
  have hsimple : IsSimpleGroup (alternatingGroup (Fin 8)) := alt8_simple
  have hO : ∀ x ∈ pClosure H, x ∈ fusionOddCore Y → x = 1 := fun x hx hxO =>
    hY.pClosure_inf_oddCore e hsw hc hx hxO
  refine ⟨ι₁.range, ι₂.range, ⟨(MonoidHom.ofInjective hι₁).symm⟩,
    ⟨(MonoidHom.ofInjective hι₂).symm⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    have : F.symm (a, 1) * F.symm (1, b) = F.symm (1, b) * F.symm (a, 1) := by
      rw [← map_mul, ← map_mul]
      congr 1
    exact congrArg Subtype.val this
  · rw [disjoint_def]
    rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
    have h1 : F.symm (a, 1) = F.symm (1, b) := Subtype.ext hb.symm
    have h2 := F.symm.injective h1
    have ha : a = 1 := (Prod.ext_iff.1 h2).1
    rw [ha, map_one]
  · rw [disjoint_def]
    rintro _ ⟨a, rfl⟩ hO'
    have : ι₁ a = 1 := hO _ (hι₁P a) hO'
    exact this
  · rw [disjoint_def]
    rintro _ ⟨a, rfl⟩ hO'
    have : ι₂ a = 1 := hO _ (hι₂P a) hO'
    exact this
  · rintro _ ⟨a, rfl⟩
    have hc1 := hY.pToProd_conj e hsw hc ⟨ι₁ a, hι₁P a⟩
    rw [← hf, hι₁F] at hc1
    simp only [map_one] at hc1
    have : (⟨t * ι₁ a * t⁻¹, (pClosure_normal H).conj_mem _ (hι₁P a) _⟩ : ↥(pClosure H)) =
        F.symm (1, f₂ a) := by
      rw [F.eq_symm_apply]
      exact hc1
    exact ⟨f₂ a, (congrArg Subtype.val this).symm⟩
  · rintro _ ⟨a, rfl⟩
    have hc1 := hY.pToProd_conj e hsw hc ⟨ι₂ a, hι₂P a⟩
    rw [← hf, hι₂F] at hc1
    simp only [map_one] at hc1
    have : (⟨t * ι₂ a * t⁻¹, (pClosure_normal H).conj_mem _ (hι₂P a) _⟩ : ↥(pClosure H)) =
        F.symm (f₁ a, 1) := by
      rw [F.eq_symm_apply]
      exact hc1
    exact ⟨f₁ a, (congrArg Subtype.val this).symm⟩
  · intro h hh
    have hhP := le_pClosure H hh
    refine ⟨ι₁ (F ⟨h, hhP⟩).1, ⟨_, rfl⟩, ι₂ (F ⟨h, hhP⟩).2, ⟨_, rfl⟩, ?_⟩
    have h1 : (⟨h, hhP⟩ : ↥(pClosure H)) = F.symm (F ⟨h, hhP⟩) := (F.symm_apply_apply _).symm
    have e2 : F ⟨h, hhP⟩ = ((F ⟨h, hhP⟩).1, 1) * (1, (F ⟨h, hhP⟩).2) := by
      ext <;> simp
    rw [e2, map_mul] at h1
    exact congrArg Subtype.val h1

end LayerHyp

end CFSG.EvenSporadicStandard.M24Std.DRes
