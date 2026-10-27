module

public import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatLayer
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatTight
public import CFSG.LocalAnalysis.RankThreeUC.GN15AltNatSetup

public section

namespace CFSG.LocalAnalysis.RankThreeUC.S15.GN15

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.B1Red CFSG.RankThree.PartTwo CFSG.QuasithinUnique
open CFSG.HardMathSupport.Meierfrankenfeld.AGL81.I56 Equiv
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry (altHeart_irreducible)
open scoped commutatorElement

section Aux

variable {V : Type*} [CommGroup V]

private theorem altNat_cg_c {G : Type*} [CommGroup G] (x w c : G) :
    x * c * (w * c)⁻¹ = x * w⁻¹ := by
  calc x * c * (w * c)⁻¹ = (x * w⁻¹) * (c * c⁻¹) := by simp only [mul_inv_rev]; ac_rfl
    _ = x * w⁻¹ := by rw [mul_inv_cancel, mul_one]

theorem altNat_commSub_smul {L : Subgroup (MulAut V)} {W : Subgroup V} {a : MulAut V}
    (haL : ∀ l ∈ L, a * l * a⁻¹ ∈ L) (haW : ∀ w ∈ W, a w ∈ W) :
    ∀ m ∈ CFSG.Quasithin.commSub W L, a m ∈ CFSG.Quasithin.commSub W L := by
  intro m hm
  induction hm using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨l, hl, w, hw, rfl⟩ := hx
    refine Subgroup.subset_closure ⟨a * l * a⁻¹, haL l hl, a w, haW w hw, ?_⟩
    simp [MulAut.mul_apply, map_mul, map_inv]
  | one => simp
  | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
  | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx

theorem altNat_commSub_le {L : Subgroup (MulAut V)} {W : Subgroup V}
    (hLW : ∀ l ∈ L, ∀ w ∈ W, l w ∈ W) : CFSG.Quasithin.commSub W L ≤ W := by
  unfold CFSG.Quasithin.commSub
  refine (Subgroup.closure_le W).2 ?_
  rintro _ ⟨l, hl, w, hw, rfl⟩
  exact W.mul_mem (hLW l hl w hw) (W.inv_mem hw)

end Aux

section Key

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem altNat_commSub_le_natU {H L : Subgroup (MulAut V)} (hLH : L ≤ H) :
    CFSG.Quasithin.commSub (fixV (pCoreOf 2 H)) L ≤ natU H := by
  unfold CFSG.Quasithin.commSub
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨x, hx, w, hw, rfl⟩
  have hxs : x ∈ stabSub (fixV (pCoreOf 2 H)) := le_stabSub_fixV_pCoreOf H (hLH hx)
  have hg : resHom (fixV (pCoreOf 2 H)) ⟨x, hxs⟩ ∈ autSub H (fixV (pCoreOf 2 H)) :=
    mem_autSub.2 ⟨⟨x, hxs⟩, hLH hx, rfl⟩
  let v : ↥(fixV (pCoreOf 2 H)) := ⟨w, hw⟩
  have hc : resHom (fixV (pCoreOf 2 H)) ⟨x, hxs⟩ v * v⁻¹ ∈
      commV (autSub H (fixV (pCoreOf 2 H))) :=
    Subgroup.subset_closure ⟨_, hg, v, rfl⟩
  exact ⟨_, hc, rfl⟩

theorem altNat_key (hV : ∀ v : V, v ^ 2 = 1)
    {H L A : Subgroup (MulAut V)} {n : ℕ} (hodd : Odd n) (h9 : 9 ≤ n)
    (e : ↥L ≃* alternatingGroup (Fin n))
    (hLH : L ≤ H) (hLn : ∀ h ∈ H, ∀ l ∈ L, h * l * h⁻¹ ∈ L) (hHA : H ≤ L ⊔ A)
    (hoff : IsFFStarOffender H A) (hLA : ⁅L, A⁆ = L)
    (α : ↥L →* alternatingGroup (Fin n)) (hα : Function.Surjective α)
    (π : ↥(natU H) →* Multiplicative (altHeart n))
    (hπk : ∀ u, π u = 1 → ∀ l ∈ L, l (u : V) = u)
    (hπi : ∀ (l : ↥L) (u v : ↥(natU H)), (v : V) = (l : MulAut V) (u : V) →
      ∀ x : evenWeight n, Multiplicative.toAdd (π u) = (QuotientAddGroup.mk x : altHeart n) →
        Multiplicative.toAdd (π v) =
          (QuotientAddGroup.mk (evenWeightPerm (α l : Perm (Fin n)) x) : altHeart n))
    (hinj : ∀ u : ↥(natU H), (u : V) ∈ CFSG.Quasithin.commSub (fixV (pCoreOf 2 H)) L →
      π u = 1 → u = 1) :
    commV L ≤ fixV (pCoreOf 2 H) := by
  classical
  have hAH : A ≤ H := hoff.1
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hoff.2.2.1.1
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [pow_two] using hoff.2.2.1.2 a ha
  have hS := altNatSetup hV (by omega) e hLH hLn hHA hAH hA2
  have hP2 : IsPGroup 2 ↥(pCoreOf 2 H) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H
  set P := pCoreOf 2 H with hPdef
  set W : Subgroup V := fixV P with hWdef
  set M : Subgroup V := CFSG.Quasithin.commSub W L with hMdef
  set A₀ : Subgroup (MulAut V) := A ⊓ centSub W with hA₀def
  have hWH : ∀ h ∈ H, ∀ w ∈ W, h w ∈ W := fixV_pCoreOf_inv
  have hA₀P : ∀ a ∈ A₀, a ∈ P := by
    intro a ha
    have : a ∈ H ⊓ centSub W := ⟨hAH ha.1, ha.2⟩
    rwa [hS.ker] at this
  have hLinvW : ∀ l ∈ L, ∀ w ∈ W, l w ∈ W := fun l hl w hw => hWH l (hLH hl) w hw
  have hMW : M ≤ W := altNat_commSub_le hLinvW
  have hMinv : ∀ l ∈ L, ∀ m ∈ M, l m ∈ M := fun l hl m hm =>
    altNat_commSub_smul (fun x hx => L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl))
      (hLinvW l hl) m hm
  have hAM : ∀ a ∈ A, ∀ m ∈ M, a m ∈ M := fun a ha m hm =>
    altNat_commSub_smul (hS.an a ha) (fun w hw => hWH a (hAH ha) w hw) m hm
  have hLperf : Group.IsPerfect ↥L := ⟨(isQuasisimple_of_alt (by omega : 5 ≤ n) e).1⟩
  have hαinj : Function.Injective α := (Finite.injective_iff_surjective_of_equiv e.toEquiv).2 hα
  have hMU : M ≤ natU H := altNat_commSub_le_natU hLH
  let πM : ↥M →* Multiplicative (altHeart n) := π.comp (Subgroup.inclusion hMU)
  have hπMinj : Function.Injective πM := by
    rw [injective_iff_map_eq_one]
    intro m hm
    have := hinj (Subgroup.inclusion hMU m) m.2 hm
    exact Subtype.ext (congrArg (fun u : ↥(natU H) => (u : V)) this)
  have hπMsurj : Function.Surjective πM := by
    let S : AddSubgroup (altHeart n) := AddSubgroup.toSubgroup'.symm πM.range
    have hmem : ∀ v : altHeart n, v ∈ S ↔ ∃ m : ↥M, πM m = Multiplicative.ofAdd v := fun v =>
      ⟨fun ⟨m, hm⟩ => ⟨m, hm⟩, fun ⟨m, hm⟩ => ⟨m, hm⟩⟩
    have hinv : ∀ σ ∈ alternatingGroup (Fin n), ∀ x : evenWeight n,
        (QuotientAddGroup.mk x : altHeart n) ∈ S →
          (QuotientAddGroup.mk (evenWeightPerm σ x) : altHeart n) ∈ S := by
      intro σ hσ x hx
      obtain ⟨m, hm⟩ := (hmem _).1 hx
      obtain ⟨l, hl⟩ := hα ⟨σ, hσ⟩
      have hσl : (α l : Perm (Fin n)) = σ := congrArg Subtype.val hl
      refine (hmem _).2 ⟨⟨(l : MulAut V) (m : V), hMinv l l.2 m m.2⟩, Multiplicative.toAdd.injective ?_⟩
      have h1 := hπi l (Subgroup.inclusion hMU m)
        (Subgroup.inclusion hMU ⟨(l : MulAut V) (m : V), hMinv l l.2 m m.2⟩) rfl x
        (congrArg Multiplicative.toAdd hm)
      rw [hσl] at h1
      exact h1
    rcases altHeart_irreducible (by omega) S hinv with h | h
    · exfalso
      have hπ1 : ∀ m : ↥M, πM m = 1 := fun m => by
        have : Multiplicative.toAdd (πM m) ∈ S := (hmem _).2 ⟨m, rfl⟩
        rw [h, AddSubgroup.mem_bot] at this
        exact Multiplicative.toAdd.injective (this.trans toAdd_one.symm)
      have hLM : ∀ l ∈ L, ∀ m ∈ M, l m = m := fun l hl m hm =>
        hπk (Subgroup.inclusion hMU ⟨m, hm⟩) (hπ1 ⟨m, hm⟩) l hl
      have hstep := altNat_perf_step hLperf (N₀ := ⊥) (D := M) (N := W)
        (fun v hv l hl => Subgroup.subset_closure ⟨l, hl, v, hv, rfl⟩)
        (fun d hd l hl => by rw [hLM l hl d hd, mul_inv_cancel]; exact Subgroup.one_mem _)
      have hLW : ∀ l ∈ L, ∀ w ∈ W, l w = w := by
        intro l hl w hw
        have := hstep w hw l hl
        rw [Subgroup.mem_bot, mul_inv_eq_one] at this
        exact this
      have hLP : L ≤ P := fun l hl => by
        have : l ∈ H ⊓ centSub W := ⟨hLH hl, fun w hw => hLW l hl w hw⟩
        rwa [hS.ker] at this
      have h2 : IsPGroup 2 ↥L := hP2.to_le hLP
      exact alt_not_two_group (by omega) (h2.of_surjective e.toMonoidHom e.surjective)
    · intro v
      have : Multiplicative.toAdd v ∈ S := by rw [h]; trivial
      obtain ⟨m, hm⟩ := (hmem _).1 this
      exact ⟨m, by simpa using hm⟩
  let ε : evenWeight n ≃+ altHeart n := AddEquiv.ofBijective (QuotientAddGroup.mk' (evenWeightOnes n))
    ⟨altHeart_mk_injective hodd, QuotientAddGroup.mk_surjective⟩
  let εm : Multiplicative (altHeart n) ≃* Multiplicative (evenWeight n) :=
    AddEquiv.toMultiplicative ε.symm
  let eM : ↥M ≃* Multiplicative (evenWeight n) :=
    (MulEquiv.ofBijective πM ⟨hπMinj, hπMsurj⟩).trans εm
  let D : AltNatModule L M n :=
    { inv := hMinv
      α := α
      surj := hα
      e := eM
      equivar := by
        intro l m m' h
        have hx : (QuotientAddGroup.mk (Multiplicative.toAdd (eM m)) : altHeart n) =
            Multiplicative.toAdd (πM m) := by
          show ε (ε.symm (Multiplicative.toAdd (πM m))) = _
          exact ε.apply_symm_apply _
        have h1 := hπi l (Subgroup.inclusion hMU m) (Subgroup.inclusion hMU m') h _ hx.symm
        show ε.symm (Multiplicative.toAdd (πM m')) = _
        rw [show Multiplicative.toAdd (πM m') =
          Multiplicative.toAdd (π (Subgroup.inclusion hMU m')) from rfl, h1]
        exact ε.symm_apply_apply _ }
  have htight := altNat_tight D hodd (by omega) hαinj hS.an hAM hMW hA2
    (fun a ha hcomm w hw => (mem_fixV.1 hw) a (hS.cl a ha hcomm))
  have hWfix : W ≤ fixV A₀ := fun w hw a ha => ha.2 w hw
  have hinfW : W ⊓ fixV A₀ = W := inf_eq_left.2 hWfix
  have hle := B1.card_inf_fixV_le hoff (inf_le_left : A₀ ≤ A) W
  have heq : Nat.card A₀ * Nat.card ↥(W ⊓ fixV A₀) = Nat.card A * Nat.card ↥(W ⊓ fixV A) := by
    rw [hinfW] at hle ⊢
    exact le_antisymm hle htight
  obtain ⟨hcardeq, hsup⟩ := B1.card_inf_fixV_eq hoff (inf_le_left : A₀ ≤ A) W heq
  rw [hinfW] at hsup
  set F : Subgroup V := fixV A₀ with hF
  have hA₀cent : ∀ a ∈ A₀, ∀ h ∈ H, a * h = h * a := by
    intro a ha h hh
    obtain ⟨l, hl, b, hb, rfl⟩ := hS.dec h hh
    have h1 : a * l = l * a := (hS.lp l hl a (hA₀P a ha)).symm
    have h2 : a * b = b * a := hAcomm a ha.1 b hb
    calc a * (l * b) = (a * l) * b := by rw [mul_assoc]
      _ = (l * a) * b := by rw [h1]
      _ = l * (a * b) := by rw [mul_assoc]
      _ = l * (b * a) := by rw [h2]
      _ = l * b * a := by rw [mul_assoc]
  have hFH : ∀ h ∈ H, ∀ f ∈ F, h f ∈ F := by
    intro h hh f hf a ha
    have := congrArg (fun g : MulAut V => g f) (hA₀cent a ha h hh)
    simp only [MulAut.mul_apply] at this
    rw [this, (mem_fixV.1 hf) a ha]
  let N : Subgroup (MulAut V) :=
    { carrier := {h | h ∈ H ∧ ∀ f ∈ F, h f * f⁻¹ ∈ W}
      one_mem' := ⟨H.one_mem, fun f _ => by simp⟩
      mul_mem' := fun {g h} hg hh => ⟨H.mul_mem hg.1 hh.1, fun f hf => by
        have h1 := hg.2 (h f) (hFH h hh.1 f hf)
        have h2 := hh.2 f hf
        have e : (g * h) f * f⁻¹ = (g (h f) * (h f)⁻¹) * (h f * f⁻¹) := by
          simp only [MulAut.mul_apply]; group
        rw [e]; exact W.mul_mem h1 h2⟩
      inv_mem' := fun {h} hh => ⟨H.inv_mem hh.1, fun f hf => by
        have hf' : h⁻¹ f ∈ F := hFH h⁻¹ (H.inv_mem hh.1) f hf
        have h1 := hh.2 (h⁻¹ f) hf'
        have e : h⁻¹ f * f⁻¹ = (h (h⁻¹ f) * (h⁻¹ f)⁻¹)⁻¹ := by
          rw [MulAut.apply_inv_self]; simp
        rw [e]; exact W.inv_mem h1⟩ }
  have hAN' : A ≤ N := by
    intro a ha
    refine ⟨hAH ha, fun f hf => ?_⟩
    have hf' : f ∈ W ⊔ fixV A := by rw [hsup]; exact hf
    obtain ⟨w, hw, c, hc, rfl⟩ := Subgroup.mem_sup.1 hf'
    have hac : a c = c := (mem_fixV.1 hc) a ha
    rw [map_mul, hac, altNat_cg_c]
    exact W.mul_mem (hWH a (hAH ha) w hw) (W.inv_mem hw)
  have hNconj : ∀ g ∈ H, ∀ n ∈ N, g * n * g⁻¹ ∈ N := by
    intro g hg n hn
    refine ⟨H.mul_mem (H.mul_mem hg hn.1) (H.inv_mem hg), fun f hf => ?_⟩
    have hu : g⁻¹ f ∈ F := hFH g⁻¹ (H.inv_mem hg) f hf
    have h1 := hn.2 (g⁻¹ f) hu
    have e : (g * n * g⁻¹) f * f⁻¹ = g (n (g⁻¹ f) * (g⁻¹ f)⁻¹) := by
      simp only [MulAut.mul_apply, map_mul, map_inv, MulAut.apply_inv_self]
    rw [e]; exact hWH g hg _ h1
  have hLN : L ≤ N := by
    rw [← hLA, Subgroup.commutator_le]
    intro l hl a ha
    have h1 : l * a * l⁻¹ ∈ N := hNconj l (hLH hl) a (hAN' ha)
    have h2 : ⁅l, a⁆ = (l * a * l⁻¹) * a⁻¹ := by rw [commutatorElement_def]
    rw [h2]
    exact N.mul_mem h1 (N.inv_mem (hAN' ha))
  have hT1 : ∀ l ∈ L, ∀ f ∈ F, l f * f⁻¹ ∈ W := fun l hl f hf => (hLN hl).2 f hf
  have hFM : ∀ f ∈ F, ∀ l ∈ L, l f * f⁻¹ ∈ M :=
    altNat_perf_step hLperf (N₀ := M) (D := W) (N := F) (fun v hv l hl => hT1 l hl v hv)
      (fun d hd l hl => Subgroup.subset_closure ⟨l, hl, d, hd, rfl⟩)
  have hcomm : ∀ l ∈ L, ∀ a ∈ A₀, l * a = a * l := fun l hl a ha => hS.lp l hl a (hA₀P a ha)
  have hA₀p : IsPGroup 2 ↥A₀ := fun a => ⟨1, by
    apply Subtype.ext
    show (a : MulAut V) ^ (2 ^ 1) = 1
    rw [pow_one, pow_two]
    exact hA2 a a.2.1⟩
  have hII : ∀ B : Subgroup (MulAut V), B ≤ A₀ →
      Nat.card B * Nat.card (fixV B) ≤ Nat.card A₀ * Nat.card (fixV A₀) := by
    intro B hB
    rw [hcardeq]
    exact hoff.card_le (hB.trans inf_le_left)
  have hMF : ∀ m ∈ M, ∀ a ∈ A₀, a m = m := fun m hm a ha => ha.2 m (hMW hm)
  have hlay := altNat_layer hV hodd (by omega) hLperf D hcomm hA₀p hII hMF hFM
  have hfin := altNat_perf_step hLperf (N₀ := W) (D := F) (N := ⊤)
    (fun v _ l hl => hlay v l hl) (fun d hd l hl => hT1 l hl d hd)
  unfold commV
  refine (Subgroup.closure_le W).2 ?_
  rintro _ ⟨x, hx, v, rfl⟩
  exact hfin v trivial x hx

end Key

end CFSG.LocalAnalysis.RankThreeUC.S15.GN15
