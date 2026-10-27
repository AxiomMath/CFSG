module

public import Certificates.Certificate397101
public import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp25SG3A
public import CFSG.ClassicalInvolution.Q3.TL3T51B

public section

namespace CFSG.ClassicalInvolution.Q8P.Asc77.P25R

open CFSG.ClassicalInvolution.Q3 CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr
open CFSG.ClassicalInvolution.Q3.TC.Thin (pSpan)
open Certificates.AE117 Certificates.AE5Sq

namespace AE5Sq

theorem finAll_iff {α : Type} {s : Finset α} {f : α → Bool} :
    finAll s f = true ↔ ∀ x ∈ s, f x = true := by
  simp [finAll]

@[expose] def Q8Rel {H : Type*} [Group H] (x y : H) : Prop :=
  x * x ≠ 1 ∧ x * x * (x * x) = 1 ∧ y * y = x * x ∧ x * y * (x * y) = x * x ∧ y ≠ x ∧ y ≠ x * x * x

theorem Q8Rel.map {H K : Type*} [Group H] [Group K] {f : H →* K} (hf : Function.Injective f) {x y : H}
    (h : Q8Rel x y) : Q8Rel (f x) (f y) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun e => h1 (hf (by rw [map_mul, e, map_one])), ?_, ?_, ?_, fun e => h5 (hf e),
    fun e => h6 (hf (by rw [e, map_mul, map_mul]))⟩
  · simpa only [map_mul, map_one] using congrArg f h2
  · simpa only [map_mul] using congrArg f h3
  · simpa only [map_mul] using congrArg f h4

theorem Q8Rel.of_map {H K : Type*} [Group H] [Group K] {f : H →* K} (hf : Function.Injective f) {x y : H}
    (h : Q8Rel (f x) (f y)) : Q8Rel x y := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨fun e => h1 (by rw [← map_mul, e, map_one]), hf ?_, hf ?_, hf ?_, fun e => h5 (by rw [e]),
    fun e => h6 (by rw [e, map_mul, map_mul])⟩
  · simpa only [map_mul, map_one] using h2
  · simpa only [map_mul] using h3
  · simpa only [map_mul] using h4

theorem ord4Pi_iff (x : Wr 5) :
    ord4Pi x = true ↔ mkQ 5 x * mkQ 5 x ≠ 1 ∧ mkQ 5 x * mkQ 5 x * (mkQ 5 x * mkQ 5 x) = 1 := by
  rw [ne_eq, ← map_mul, ← map_mul, ← TL4.Mdl117.inPi_iff, ← TL4.Mdl117.inPi_iff]
  simp [ord4Pi]

theorem q8Pair_iff (x y : Wr 5) : q8Pair x y = true ↔ Q8Rel (mkQ 5 x) (mkQ 5 y) := by
  unfold q8Pair Q8Rel
  simp only [Bool.and_eq_true, Bool.not_eq_true', ord4Pi_iff, ← Bool.not_eq_true, TL4.Mdl117.eqPi_iff, map_mul]
  tauto

theorem evalG_mem {G : Type*} [Group G] {H : Subgroup G} {gens : List G} (hg : ∀ g ∈ gens, g ∈ H)
    (w : List ℕ) : evalG gens w ∈ H := by
  unfold evalG
  have hget : ∀ k, gens.getD k 1 ∈ H := by
    intro k
    rw [List.getD_eq_getElem?_getD]
    cases h : gens[k]? with
    | none => exact H.one_mem
    | some g => exact hg g (List.mem_of_getElem? h)
  suffices ∀ acc : G, acc ∈ H → w.foldl (fun acc k =>
      acc * if k % 2 = 0 then gens.getD (k / 2) 1 else (gens.getD (k / 2) 1)⁻¹) acc ∈ H from
    this 1 H.one_mem
  induction w with
  | nil => exact fun acc h => h
  | cons k w ih =>
    intro acc hacc
    apply ih
    show acc * (if k % 2 = 0 then gens.getD (k / 2) 1 else (gens.getD (k / 2) 1)⁻¹) ∈ H
    split_ifs
    · exact H.mul_mem hacc (hget _)
    · exact H.mul_mem hacc (H.inv_mem (hget _))

theorem mem_alphas : ∀ α : Finset (Fin 5), α.card = 4 → α ∈ alphas := by decide

theorem card_of_mem_alphas : ∀ α ∈ alphas, α.card = 4 := by decide

theorem exists_lift (g : ↥(TL4.aeModel 5)) :
    ∃ x : Wr 5, x.vec ∈ evenFin5 () ∧ x.perm ∈ a5Fin () ∧ mkQ 5 x = g := by
  obtain ⟨x, hx, hxg⟩ := Subgroup.mem_map.1 g.2
  obtain ⟨h1, h2⟩ := mem_aeSub.1 hx
  refine ⟨x, ?_, ?_, hxg⟩
  · simp only [evenFin5, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h1
  · simp only [a5Fin, Finset.mem_filter, Finset.mem_univ, true_and]
    exact h2

theorem mkQ_mem_memBar_of_inMem {α : Finset (Fin 5)} (h : α.card = 4) {b : Bool} {x : Wr 5}
    (hx : inMem α b x = true) : mkQ 5 x ∈ memBar α h b := by
  obtain ⟨m, hm, hmx⟩ := List.any_eq_true.1 hx
  exact (TL4.Mdl117.mem_memBar_iff α h b _).2 ⟨m, hm, (TL4.Mdl117.eqPi_iff m x).1 hmx⟩

theorem genOK_spec {α : Finset (Fin 5)} (hα : α ∈ alphas) (b : Bool) :
    (memAtL α b).getD 2 1 ∈ memAtL α b ∧ (memAtL α b).getD 4 1 ∈ memAtL α b ∧
      q8Pair ((memAtL α b).getD 2 1) ((memAtL α b).getD 4 1) = true ∧
      ∀ m ∈ memAtL α b, ∃ w ∈ words8,
        eqPi (evalG [(memAtL α b).getD 2 1, (memAtL α b).getD 4 1] w) m = true := by
  have hcheck := Certificates.certificate397101
  simp only [Certificates.AE5Sq.check, Bool.and_eq_true] at hcheck
  have hg := hcheck.1.1.2
  simp only [genOK, List.all_eq_true] at hg
  have h1 := hg α hα b (by cases b <;> simp)
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.any_eq_true] at h1
  exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩

theorem pairsOK_spec {x y : Wr 5} (hxv : x.vec ∈ evenFin5 ())
    (hxp : x.perm ∈ a5Fin ()) (hyv : y.vec ∈ evenFin5 ()) (hyp : y.perm ∈ a5Fin ())
    (hq : q8Pair x y = true) : ∃ α ∈ alphas, ∃ b : Bool, inMem α b x = true ∧ inMem α b y = true := by
  have hcheck := Certificates.certificate397101
  simp only [Certificates.AE5Sq.check, Bool.and_eq_true] at hcheck
  have hp := hcheck.1.2
  unfold pairsOK at hp
  have h1 := (finAll_iff.1 ((finAll_iff.1 hp) x.perm hxp)) x.vec hxv
  have hx4 : ord4Pi ⟨x.vec, x.perm⟩ = true := by
    have := ((q8Pair_iff x y).1 hq).1
    have h2 := ((q8Pair_iff x y).1 hq).2.1
    exact (ord4Pi_iff x).2 ⟨this, h2⟩
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h1
  rcases h1 with h1 | h1
  · rw [hx4] at h1
    exact absurd h1 (by decide)
  have h2 := (finAll_iff.1 ((finAll_iff.1 h1) y.perm hyp)) y.vec hyv
  rw [Bool.or_eq_true, Bool.not_eq_true'] at h2
  rcases h2 with h2 | h2
  · rw [hq] at h2
    exact absurd h2 (by decide)
  obtain ⟨α, hα, hb⟩ := List.any_eq_true.1 h2
  obtain ⟨b, -, hb⟩ := List.any_eq_true.1 hb
  rw [Bool.and_eq_true] at hb
  exact ⟨α, hα, b, hb.1, hb.2⟩

theorem sqOK_spec (c : Wr 5)
    (ha : eqPi (c * c * (c * c) * a0 ()) (a0 () * (c * c * (c * c))) = true)
    (hb : eqPi (c * c * (c * c) * b0 ()) (b0 () * (c * c * (c * c))) = true) :
    ∃ α ∈ alphas, ∃ b : Bool, ∃ y ∈ memAtL α b, ord4Pi y = true ∧ eqPi (c * c * y) (y * (c * c)) = true := by
  have hcheck := Certificates.certificate397101
  simp only [Certificates.AE5Sq.check, Bool.and_eq_true] at hcheck
  have hs := hcheck.2
  unfold sqOK at hs
  have h1 := (finAll_iff.1 ((finAll_iff.1 hs) c.perm (Finset.mem_univ _))) c.vec (Finset.mem_univ _)
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at h1
  rcases h1 with h1 | h1
  · exfalso
    revert h1
    rw [Bool.and_eq_false_iff]
    rintro (h | h)
    · exact absurd ha (by rw [h]; decide)
    · exact absurd hb (by rw [h]; decide)
  obtain ⟨α, hα, hb'⟩ := List.any_eq_true.1 h1
  obtain ⟨b, -, hb'⟩ := List.any_eq_true.1 hb'
  obtain ⟨y, hy, hy'⟩ := List.any_eq_true.1 hb'
  rw [Bool.and_eq_true] at hy'
  exact ⟨α, hα, b, y, hy, hy'.1, hy'.2⟩

theorem gens_spec :
    (a0 ()).vec ∈ evenFin5 () ∧ (a0 ()).perm ∈ a5Fin () ∧ (b0 ()).vec ∈ evenFin5 () ∧
      (b0 ()).perm ∈ a5Fin () := by
  have hcheck := Certificates.certificate397101
  simp only [Certificates.AE5Sq.check, Bool.and_eq_true, decide_eq_true_eq] at hcheck
  exact ⟨hcheck.1.1.1.1.1.1, hcheck.1.1.1.1.1.2, hcheck.1.1.1.1.2, hcheck.1.1.1.2⟩

theorem mkQ_mem_aeModel {x : Wr 5} (hv : x.vec ∈ evenFin5 ()) (hp : x.perm ∈ a5Fin ()) :
    mkQ 5 x ∈ TL4.aeModel 5 := by
  refine Subgroup.mem_map_of_mem (mkQ 5) (mem_aeSub.2 ⟨?_, ?_⟩)
  · show ∑ i, x.vec i = 0
    simpa [evenFin5] using hv
  · simpa [a5Fin] using hp

theorem memberPerm (β : MulAut ↥(TL4.aeModel 5)) (α : Finset (Fin 5))
    (h : α.card = 4) (b : Bool) :
    ∃ (α' : Finset (Fin 5)) (h' : α'.card = 4) (b' : Bool),
      ((memBar α h b).subgroupOf (TL4.aeModel 5)).map β.toMonoidHom =
        (memBar α' h' b').subgroupOf (TL4.aeModel 5) := by
  have hα := mem_alphas α h
  obtain ⟨hi, hj, hq, hw⟩ := genOK_spec hα b
  set i := (memAtL α b).getD 2 1 with hi_def
  set j := (memAtL α b).getD 4 1 with hj_def
  have hmemB : ∀ m ∈ memAtL α b, mkQ 5 m ∈ memBar α h b := fun m hm =>
    (TL4.Mdl117.mem_memBar_iff α h b _).2 ⟨m, hm, rfl⟩
  have hle : memBar α h b ≤ TL4.aeModel 5 := TL4.Mdl117.memBar_le_GBar α h b
  let ib : ↥(TL4.aeModel 5) := ⟨mkQ 5 i, hle (hmemB i hi)⟩
  let jb : ↥(TL4.aeModel 5) := ⟨mkQ 5 j, hle (hmemB j hj)⟩
  have hq0 : Q8Rel ib jb :=
    Q8Rel.of_map (f := (TL4.aeModel 5).subtype) Subtype.coe_injective ((q8Pair_iff i j).1 hq)
  have hq1 : Q8Rel (β ib) (β jb) := Q8Rel.map (f := β.toMonoidHom) β.injective hq0
  obtain ⟨x, hxv, hxp, hx⟩ := exists_lift (β ib)
  obtain ⟨y, hyv, hyp, hy⟩ := exists_lift (β jb)
  have hq2 : q8Pair x y = true := by
    rw [q8Pair_iff, hx, hy]
    exact Q8Rel.map (f := (TL4.aeModel 5).subtype) Subtype.coe_injective hq1
  obtain ⟨α', hα', b', hxm, hym⟩ := pairsOK_spec hxv hxp hyv hyp hq2
  have h' := card_of_mem_alphas α' hα'
  refine ⟨α', h', b', ?_⟩
  have hle' : memBar α' h' b' ≤ TL4.aeModel 5 := TL4.Mdl117.memBar_le_GBar α' h' b'
  have hX : ((β ib : ↥(TL4.aeModel 5)) : AEQ 5) ∈ memBar α' h' b' := hx ▸ mkQ_mem_memBar_of_inMem h' hxm
  have hY : ((β jb : ↥(TL4.aeModel 5)) : AEQ 5) ∈ memBar α' h' b' := hy ▸ mkQ_mem_memBar_of_inMem h' hym
  have hsub : ((memBar α h b).subgroupOf (TL4.aeModel 5)).map β.toMonoidHom ≤
      (memBar α' h' b').subgroupOf (TL4.aeModel 5) := by
    intro g' hg'
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hg'
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    obtain ⟨m, hm, hmg⟩ := (TL4.Mdl117.mem_memBar_iff α h b _).1 hg
    obtain ⟨w, -, hw'⟩ := hw m hm
    have hgw : g = evalG [ib, jb] w := by
      apply Subtype.ext
      have h1 : ((evalG [ib, jb] w : ↥(TL4.aeModel 5)) : AEQ 5) = evalG [mkQ 5 i, mkQ 5 j] w :=
        TL4.Mdl117.evalG_map (TL4.aeModel 5).subtype [ib, jb] w
      have h2 : mkQ 5 (evalG [i, j] w) = evalG [mkQ 5 i, mkQ 5 j] w :=
        TL4.Mdl117.evalG_map (mkQ 5) [i, j] w
      rw [h1, ← h2, ← hmg]
      exact ((TL4.Mdl117.eqPi_iff _ _).1 hw').symm
    rw [hgw]
    have h3 : ((β.toMonoidHom (evalG [ib, jb] w) : ↥(TL4.aeModel 5)) : AEQ 5) =
        evalG [((β ib : ↥(TL4.aeModel 5)) : AEQ 5), ((β jb : ↥(TL4.aeModel 5)) : AEQ 5)] w := by
      rw [TL4.Mdl117.evalG_map β.toMonoidHom]
      exact TL4.Mdl117.evalG_map (TL4.aeModel 5).subtype _ w
    rw [h3]
    apply evalG_mem
    intro g hg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with rfl | rfl
    · exact hX
    · exact hY
  apply Subgroup.eq_of_le_of_card_ge hsub
  rw [Subgroup.card_map_of_injective (f := β.toMonoidHom) β.injective,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle').toEquiv, natCard_memBar (by norm_num),
    natCard_memBar (by norm_num)]

theorem aut_eq_conj (β : MulAut ↥(TL4.aeModel 5)) :
    ∃ x : AEQ 5, ∀ g : ↥(TL4.aeModel 5), ((β g : ↥(TL4.aeModel 5)) : AEQ 5) = x * g * x⁻¹ :=
  TC.Thin.model117At_of_five_le le_rfl β (memberPerm β)

end AE5Sq

open AE5Sq in
theorem ae5SqModel_of_cert : AE5SqModel := by
  intro X _ _ Φ hS I hker β hβ
  have htop : pSpan Φ = ⊤ := hS.gen
  have hinj : Function.Injective I.φ := (MonoidHom.ker_eq_bot_iff _).1 hker
  let e : X ≃* ↥(TL4.aeModel 5) :=
    (Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)).trans
      ((MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr I.range_eq))
  have he : ∀ (x : X) (hx : x ∈ pSpan Φ), ((e x : ↥(TL4.aeModel 5)) : AEQ 5) = I.φ ⟨x, hx⟩ :=
    fun _ _ => rfl
  let β' : MulAut ↥(TL4.aeModel 5) := (e.symm.trans β).trans e
  have hβ' : ∀ x : X, β' (e x) = e (β x) := fun x => by
    show e (β (e.symm (e x))) = e (β x)
    rw [MulEquiv.symm_apply_apply]
  obtain ⟨xq, hxq⟩ := aut_eq_conj β'
  obtain ⟨c, hc⟩ : ∃ c : Wr 5, mkQ 5 c = xq := QuotientGroup.mk_surjective xq
  have hconj4 : ∀ g : ↥(TL4.aeModel 5),
      mkQ 5 (c * c * (c * c)) * (g : AEQ 5) = (g : AEQ 5) * mkQ 5 (c * c * (c * c)) := by
    intro g
    obtain ⟨x, rfl⟩ := e.surjective g
    have h := congrArg Subtype.val (show β' (β' (β' (β' (e x)))) = e x by rw [hβ', hβ', hβ', hβ', hβ x])
    rw [hxq, hxq, hxq, hxq] at h
    rw [map_mul, map_mul, hc]
    calc xq * xq * (xq * xq) * ((e x : ↥(TL4.aeModel 5)) : AEQ 5)
        = (xq * (xq * (xq * (xq * ((e x : ↥(TL4.aeModel 5)) : AEQ 5) * xq⁻¹) * xq⁻¹) * xq⁻¹) * xq⁻¹) *
            (xq * xq * (xq * xq)) := by group
      _ = ((e x : ↥(TL4.aeModel 5)) : AEQ 5) * (xq * xq * (xq * xq)) := by rw [h]
  obtain ⟨ha0v, ha0p, hb0v, hb0p⟩ := gens_spec
  have hA := hconj4 ⟨mkQ 5 (a0 ()), mkQ_mem_aeModel ha0v ha0p⟩
  have hB := hconj4 ⟨mkQ 5 (b0 ()), mkQ_mem_aeModel hb0v hb0p⟩
  obtain ⟨α, hα, b, y, hy, hy4, hyc⟩ := sqOK_spec c
    ((TL4.Mdl117.eqPi_iff _ _).2 (by rw [map_mul, map_mul]; exact hA))
    ((TL4.Mdl117.eqPi_iff _ _).2 (by rw [map_mul, map_mul]; exact hB))
  have h := card_of_mem_alphas α hα
  have hyB : mkQ 5 y ∈ memBar α h b := (TL4.Mdl117.mem_memBar_iff α h b _).2 ⟨y, hy, rfl⟩
  obtain ⟨L, hL, hLmap⟩ := I.label_surj α h b
  rw [← hLmap] at hyB
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.1 hyB
  have hez : ((e (z : X) : ↥(TL4.aeModel 5)) : AEQ 5) = mkQ 5 y := by
    rw [he _ z.2]
    exact hzy
  refine ⟨L, hL, (z : X), Subgroup.mem_subgroupOf.1 hz, ?_, ?_⟩
  · obtain ⟨h2, h4⟩ := (ord4Pi_iff y).1 hy4
    rw [← MulEquiv.orderOf_eq e, ← Subgroup.orderOf_coe, hez]
    have := orderOf_eq_prime_pow (p := 2) (n := 1) (x := mkQ 5 y)
      (by rw [pow_one, pow_two]; exact h2)
      (by rw [show (2 : ℕ) ^ (1 + 1) = 2 + 2 by norm_num, pow_add, pow_two]; exact h4)
    rw [this]
    norm_num
  · apply e.injective
    rw [← hβ', ← hβ']
    apply Subtype.ext
    rw [hxq, hxq, hez]
    have hyc' := (TL4.Mdl117.eqPi_iff _ _).1 hyc
    simp only [map_mul, hc] at hyc'
    calc xq * (xq * mkQ 5 y * xq⁻¹) * xq⁻¹ = xq * xq * mkQ 5 y * xq⁻¹ * xq⁻¹ := by group
      _ = mkQ 5 y * (xq * xq) * xq⁻¹ * xq⁻¹ := by rw [hyc']
      _ = mkQ 5 y := by group

end CFSG.ClassicalInvolution.Q8P.Asc77.P25R
