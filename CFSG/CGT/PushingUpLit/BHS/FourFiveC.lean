module

public import CFSG.CGT.PushingUpLit.BHS.FourFiveB

public section

namespace CFSG.CGT.PushingUpLit.BHS

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.RankThree.PartOne CFSG.Open CFSG.LieType.BorelTits

section Basic

variable {V : Type} [CommGroup V]

@[expose] def kerW (L B : Subgroup (MulAut V)) : Subgroup (MulAut V) :=
  (L ⊔ B) ⊓ cenSection (commV L ⊔ fixV (L ⊔ B)) (fixV (L ⊔ B))

theorem mem_kerW {L B : Subgroup (MulAut V)} {g : MulAut V} : g ∈ kerW L B ↔ g ∈ L ⊔ B ∧
    (∀ w : V, w ∈ commV L ⊔ fixV (L ⊔ B) ↔ g w ∈ commV L ⊔ fixV (L ⊔ B)) ∧
    ∀ w ∈ commV L ⊔ fixV (L ⊔ B), g w * w⁻¹ ∈ fixV (L ⊔ B) := Iff.rfl

theorem kerW_le (L B : Subgroup (MulAut V)) : kerW L B ≤ L ⊔ B := inf_le_left

end Basic

section Main

variable {V : Type} [CommGroup V] [Finite V]

namespace Hyp413Comm

variable {P : Subgroup (MulAut V)} {D : Set (Subgroup (MulAut V))}
  {T M L A B : Subgroup (MulAut V)} {n : ℕ}

theorem sectionW (d : Hyp413Comm P D M L A B n) :
    IsSLNatSection L (commV L ⊔ fixV (L ⊔ B)) (fixV (L ⊔ B)) n := by
  have hsec := d.sl.of_sup_eq_top
    (fun x hx p hp => d.invariant x (Subgroup.mem_sup_left hx) p hp) d.sup_fixV_eq_top
  rwa [d.inf_fixV_eq] at hsec

theorem card_W (d : Hyp413Comm P D M L A B n) :
    Nat.card ↥(commV L ⊔ fixV (L ⊔ B)) = (2 ^ n) ^ 2 * Nat.card ↥(fixV (L ⊔ B)) := by
  have hmul := card_sup_mul_card_inf' (X := commV L ⊔ fixV (L ⊔ B)) (Y := fixV L)
    fun a _ b _ => mul_comm a b
  rw [d.sup_fixV_eq_top, Subgroup.card_top, d.inf_fixV_eq, d.card_V_star, d.card_fixV] at hmul
  have hpos : 0 < 2 ^ n * Nat.card ↥(fixV (L ⊔ B)) := Nat.mul_pos (by positivity) Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  rw [← hmul]
  ring

theorem mem_W_iff (d : Hyp413Comm P D M L A B n) {g : MulAut V} (hg : g ∈ L ⊔ B) (w : V) :
    w ∈ commV L ⊔ fixV (L ⊔ B) ↔ g w ∈ commV L ⊔ fixV (L ⊔ B) :=
  ⟨d.invariant g hg w, fun hcw => by
    have := d.invariant g⁻¹ ((L ⊔ B).inv_mem hg) _ hcw
    rwa [MulAut.inv_apply_self] at this⟩

theorem kerW_normal (d : Hyp413Comm P D M L A B n) {g k : MulAut V} (hg : g ∈ L ⊔ B)
    (hk : k ∈ kerW L B) : g * k * g⁻¹ ∈ kerW L B := by
  obtain ⟨hkLB, hkW, hkF⟩ := mem_kerW.1 hk
  have hginv : g⁻¹ ∈ L ⊔ B := (L ⊔ B).inv_mem hg
  refine mem_kerW.2 ⟨(L ⊔ B).mul_mem ((L ⊔ B).mul_mem hg hkLB) hginv, fun w => ?_, fun w hw => ?_⟩
  · show w ∈ commV L ⊔ fixV (L ⊔ B) ↔ g (k (g⁻¹ w)) ∈ commV L ⊔ fixV (L ⊔ B)
    rw [← d.mem_W_iff hg, ← hkW, ← d.mem_W_iff hginv]
  · have hw' : g⁻¹ w ∈ commV L ⊔ fixV (L ⊔ B) := d.invariant g⁻¹ hginv w hw
    have hf := hkF _ hw'
    have hgf : g (k (g⁻¹ w) * (g⁻¹ w)⁻¹) = k (g⁻¹ w) * (g⁻¹ w)⁻¹ := hf g hg
    rw [map_mul, map_inv, MulAut.apply_inv_self] at hgf
    show g (k (g⁻¹ w)) * w⁻¹ ∈ fixV (L ⊔ B)
    rw [hgf]
    exact hf

theorem commV_kerW_le (d : Hyp413Comm P D M L A B n) :
    commV (kerW L B) ≤ commV L ⊔ fixV (L ⊔ B) :=
  (B19.commV_mono (kerW_le L B)).trans (le_sup_left.trans d.commV_sup_LB.le)

theorem isPGroup_kerW (d : Hyp413Comm P D M L A B n) (hV : ∀ v : V, v ^ 2 = 1) :
    IsPGroup 2 (kerW L B) := by
  intro k
  refine ⟨2, Subtype.ext ?_⟩
  have hk := k.2
  obtain ⟨hkLB, -, hkF⟩ := mem_kerW.1 hk
  have h4 : (k : MulAut V) ^ 4 = 1 :=
    pow_four_eq_one_of_series (Z := fixV (L ⊔ B)) (W := commV L ⊔ fixV (L ⊔ B)) hV
      (fun z hz => hz _ hkLB) hkF fun v => d.commV_kerW_le (G6.mem_commV_of_mem hk v)
  simpa using h4

theorem kerW_mem_fixV_AB (d : Hyp413Comm P D M L A B n) {k : MulAut V}
    (hk : k ∈ kerW L B) {x : V} (hx : x ∈ fixV (A ⊔ B)) : k x ∈ fixV (A ⊔ B) := by
  obtain ⟨-, -, hkF⟩ := mem_kerW.1 hk
  have hXW : fixV (A ⊔ B) ≤ commV L ⊔ fixV (L ⊔ B) := by
    rw [← d.commV_sup_eq]
    exact sup_le_sup_right (B19.commV_mono d.leA) _
  have hFX : fixV (L ⊔ B) ≤ fixV (A ⊔ B) := fixV_anti (sup_le_sup_right d.leA B)
  have h1 : k x * x⁻¹ ∈ fixV (A ⊔ B) := hFX (hkF x (hXW hx))
  have h2 : k x = (k x * x⁻¹) * x := by rw [inv_mul_cancel_right]
  rw [h2]
  exact mul_mem h1 hx

theorem kerW_le_M (h : Hyp43 P D T M) (_hV : ∀ v : V, v ^ 2 = 1)
    (d : Hyp413Comm P D M L A B n) (hAT : A ≤ T) (hBT : B ≤ T) : kerW L B ≤ M := by
  have hKP : kerW L B ≤ P := (kerW_le L B).trans (sup_le d.lam.1 (h.le B d.memB))
  set ET : Subgroup (MulAut V) := ⨆ X ∈ dInter D T, X
  have hET2 := four_seven h.toHyp41 h.syl
  have hETle : ∀ X ∈ dInter D T, X ≤ ET := fun X hX =>
    le_iSup₂_of_le (f := fun (Y : Subgroup (MulAut V)) (_ : Y ∈ dInter D T) => Y) X hX le_rfl
  have hETP : ET ≤ P := iSup₂_le fun X hX => h.le X hX.1
  have hABle : A ⊔ B ≤ ET := sup_le (hETle A ⟨d.memA, hAT⟩) (hETle B ⟨d.memB, hBT⟩)
  have hUX : commV ET ≤ fixV (A ⊔ B) := hET2.2.trans (fixV_anti hABle)
  have hKU : ∀ k ∈ kerW L B, ∀ v ∈ commV ET, k v ∈ commV ET := by
    intro k hk v hv
    have hkP : k ∈ P := hKP hk
    have hAB : conjSub k (A ⊔ B) = A ⊔ B :=
      h.conjSub_sup_eq d.memA d.memB d.ne d.comm hkP fun x hx => d.kerW_mem_fixV_AB hk hx
    have hvX : v ∈ commV A ⊔ fixV (L ⊔ B) := by
      rw [d.commV_sup_eq]
      exact hUX hv
    obtain ⟨u, hu, f, hf, rfl⟩ := Subgroup.mem_sup.1 hvX
    have hkf : k f = f := hf k (kerW_le L B hk)
    have hcu : u ∈ commV (A ⊔ B) := B19.commV_mono le_sup_left hu
    have hkcu : k u ∈ commV (A ⊔ B) := by
      have h1 : commV (conjSub k (A ⊔ B)) = (commV (A ⊔ B)).map k.toMonoidHom :=
        B19.commV_map_conj k (A ⊔ B)
      rw [hAB] at h1
      rw [h1]
      exact ⟨u, hcu, rfl⟩
    have hmem : k u * u⁻¹ ∈ commV ET := B19.commV_mono hABle (mul_mem hkcu (inv_mem hcu))
    have e : k (u * f) = (k u * u⁻¹) * (u * f) := by
      rw [map_mul, hkf]
      group
    rw [e]
    exact mul_mem hmem hv
  have hKU' : ∀ k ∈ kerW L B, (commV ET).map k.toMonoidHom = commV ET := by
    intro k hk
    refine Subgroup.eq_of_le_of_card_ge ?_ (Subgroup.card_map_of_injective k.injective).ge
    rintro _ ⟨v, hv, rfl⟩
    exact hKU k hk v hv
  have hcommEk : ∀ k ∈ kerW L B, commV (conjSub k ET) = commV ET := fun k hk =>
    (B19.commV_map_conj k ET).trans (hKU' k hk)
  have hUfix : ∀ k ∈ kerW L B, commV ET ≤ fixV (conjSub k ET) := by
    intro k hk
    have h1 : fixV (conjSub k ET) = (fixV ET).map k.toMonoidHom := Glauberman.fixV_map_conj k ET
    rw [h1]
    calc commV ET = (commV ET).map k.toMonoidHom := (hKU' k hk).symm
      _ ≤ (fixV ET).map k.toMonoidHom := Subgroup.map_mono hET2.2
  set F : Set (Subgroup (MulAut V)) := {Z | ∃ k ∈ kerW L B, Z = conjSub k ET}
  have hcommF : ∀ Z ∈ F, ∀ Z' ∈ F, ∀ x ∈ Z, ∀ y ∈ Z', x * y = y * x := by
    rintro _ ⟨k, hk, rfl⟩ _ ⟨k', hk', rfl⟩ x hx y hy
    refine comm_of_trivial_series (X := commV ET) (fun u hu => hUfix k hk hu x hx)
      (fun u hu => hUfix k' hk' hu y hy) (fun v => ?_) (fun v => ?_)
    · have := G6.mem_commV_of_mem hx v
      rwa [hcommEk k hk] at this
    · have := G6.mem_commV_of_mem hy v
      rwa [hcommEk k' hk'] at this
  have hcomm := FourOneTools.comm_of_mem_sSup hcommF
  have hsq : ∀ x ∈ sSup F, x ^ 2 = 1 := by
    refine FourOneTools.sq_eq_one_of_mem_sSup hcomm ?_
    rintro _ ⟨k, hk, rfl⟩ x hx
    obtain ⟨y, hy, rfl⟩ := hx
    show (k * y * k⁻¹) ^ 2 = 1
    rw [conj_pow, hET2.1.2 y hy, mul_one, mul_inv_cancel]
  have hE'2 : IsPGroup 2 (sSup F : Subgroup (MulAut V)) :=
    isPGroup_of_isElemAbelian2 ⟨hcomm, hsq⟩
  have hE'P : sSup F ≤ P := by
    refine sSup_le ?_
    rintro _ ⟨k, hk, rfl⟩
    exact Glauberman.map_conj_le (hKP hk) hETP
  have hETE' : ET ≤ sSup F := by
    have h1 : conjSub 1 ET ≤ sSup F := le_sSup ⟨1, (kerW L B).one_mem, rfl⟩
    rwa [conjSub_one] at h1
  have hd : dInter D (sSup F) = dInter D T :=
    h.toHyp42.dInter_eq_of_le hE'P hE'2 fun X hX => (hETle X hX).trans hETE'
  have hconjT : ∀ k ∈ kerW L B, ∀ X ∈ dInter D T, conjSub k X ∈ dInter D T := by
    intro k hk X hX
    have h1 : conjSub k X ∈ dInter D (sSup F) :=
      ⟨h.conj_mem X hX.1 k (hKP hk),
        (conjSub_mono k (hETle X hX)).trans (le_sSup ⟨k, hk, rfl⟩)⟩
    rwa [hd] at h1
  intro k hk
  refine h.normSet_le ⟨hKP hk, fun X => ⟨fun hX => hconjT k hk X hX, fun hX => ?_⟩⟩
  have h1 := hconjT k⁻¹ ((kerW L B).inv_mem hk) _ hX
  rwa [FourTwoTools.conjSub_inv_conjSub] at h1

end Hyp413Comm

end Main

end CFSG.CGT.PushingUpLit.BHS
