module

public import CFSG.ClassicalInvolution.Q3.TL3T51B
public import CFSG.ClassicalInvolution.Q3.Sec13End16M
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

set_option linter.unusedSectionVars false

namespace CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c

open CFSG CFSG.Open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Asc77 CFSG.ClassicalInvolution.Disconnected.AschTight
open CFSG.ClassicalInvolution.Q3.TC.Thin CFSG.ClassicalInvolution.Q3.AE
open CFSG.ClassicalInvolution.Q3

variable {G : Type} [Group G] [Finite G] {P : Set (Subgroup G)} {n : ℕ}

section Vec

variable {n : ℕ}

theorem zmod2 : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

theorem memBar_le (α : Finset (Fin n)) (h : α.card = 4) (b : Bool) :
    AE.memBar α h b ≤ (AE.aeSub n).map (AE.mkQ n) := by
  unfold AE.memBar
  apply Subgroup.map_mono
  unfold AE.memAt
  cases b
  · exact AE.memKStar_le_aeSub _
  · exact AE.memK_le_aeSub _

theorem centralizer_eq_one (hn5 : 5 ≤ n) (x : AE.AEQ n)
    (hx : ∀ y ∈ (AE.aeSub n).map (AE.mkQ n), x * y = y * x) : x = 1 := by
  have hev : ∀ f : Fin n → ZMod 2, ∑ i, f i = 0 →
      x * AE.mkQ n (AE.Wr.ofVec f) = AE.mkQ n (AE.Wr.ofVec f) * x := by
    intro f hf
    apply hx
    refine ⟨AE.Wr.ofVec f, AE.mem_aeSub.mpr ⟨?_, ?_⟩, rfl⟩
    · exact hf
    · rw [AE.Wr.ofVec, Equiv.Perm.sign_one]
  obtain ⟨v, hv⟩ := AE.eq_vec_of_comm_vectors hn5 hev
  have hcm : ∀ (α : Finset (Fin n)) (h : α.card = 4) (b : Bool),
      ∀ y ∈ AE.memBar α h b, AE.mkQ n (AE.Wr.ofVec v) * y = y * AE.mkQ n (AE.Wr.ofVec v) := by
    intro α h b y hy
    rw [← hv]
    exact hx y (memBar_le α h b hy)
  have hconst : ∀ i j : Fin n, v i = v j := by
    intro i j
    obtain ⟨α, hiα, -, hα⟩ := Finset.exists_subsuperset_card_eq (n := 4)
      (Finset.subset_univ ({i, j} : Finset (Fin n)))
      (Finset.card_le_two.trans (by norm_num))
      (by rw [Finset.card_univ, Fintype.card_fin]; omega)
    have hc := (AE.vec_centralizes_memBar_iff hn5 α hα true v).mp (hcm α hα true)
    exact hc i (hiα (by simp)) j (hiα (by simp))
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  rcases zmod2 (v i₀) with h0 | h1
  · have hv0 : v = 0 := funext fun i => (hconst i i₀).trans h0
    rw [hv, hv0]
    rfl
  · have hv1 : v = fun _ => 1 := funext fun i => (hconst i i₀).trans h1
    rw [hv, hv1]
    have : AE.Wr.ofVec (fun _ : Fin n => (1 : ZMod 2)) = AE.Wr.allOnes n := rfl
    rw [this]
    exact (QuotientGroup.eq_one_iff _).mpr (AE.mem_piSub.mpr (Or.inr rfl))

@[expose] def ind (S : Finset (Fin n)) : Fin n → ZMod 2 := fun m => if m ∈ S then 1 else 0

theorem zBar_eq (α : Finset (Fin n)) (h : α.card = 4) :
    AE.zBar α h = AE.mkQ n (AE.Wr.ofVec (ind α)) := by
  unfold AE.zBar
  congr 1
  refine AE.Wr.ext ?_ ?_
  · funext m
    show (AE.zOf (AE.emb α h)).vec m = if m ∈ α then 1 else 0
    rw [AE.zOf_vec_apply]
    simp [AE.range_emb]
  · show (AE.zOf (AE.emb α h)).perm = 1
    simp [AE.zOf, AE.embed_perm, AE.zQ, AE.embedPerm_one]

theorem ofVec_add (f g : Fin n → ZMod 2) :
    AE.mkQ n (AE.Wr.ofVec (f + g)) = AE.mkQ n (AE.Wr.ofVec f) * AE.mkQ n (AE.Wr.ofVec g) := by
  rw [← map_mul]
  exact congrArg (AE.mkQ n) (AE.Wr.ext (funext fun m => rfl) rfl)

theorem eq_vec_of_comm_zBar (hn5 : 5 ≤ n) (x : AE.AEQ n)
    (hx : ∀ (α : Finset (Fin n)) (h : α.card = 4), x * AE.zBar α h = AE.zBar α h * x) :
    ∃ v : Fin n → ZMod 2, x = AE.mkQ n (AE.Wr.ofVec v) := by
  classical
  let C : AddSubmonoid (Fin n → ZMod 2) :=
    { carrier := {f | x * AE.mkQ n (AE.Wr.ofVec f) = AE.mkQ n (AE.Wr.ofVec f) * x}
      add_mem' := fun {f g} hf hg => by
        have hf' : x * AE.mkQ n (AE.Wr.ofVec f) = AE.mkQ n (AE.Wr.ofVec f) * x := hf
        have hg' : x * AE.mkQ n (AE.Wr.ofVec g) = AE.mkQ n (AE.Wr.ofVec g) * x := hg
        show x * AE.mkQ n (AE.Wr.ofVec (f + g)) = AE.mkQ n (AE.Wr.ofVec (f + g)) * x
        rw [ofVec_add, ← mul_assoc, hf', mul_assoc, hg', ← mul_assoc]
      zero_mem' := by
        show x * AE.mkQ n (AE.Wr.ofVec 0) = AE.mkQ n (AE.Wr.ofVec 0) * x
        rw [show AE.Wr.ofVec (0 : Fin n → ZMod 2) = 1 from rfl, map_one, mul_one, one_mul] }
  have hsmul : ∀ (c : ZMod 2) (f : Fin n → ZMod 2), f ∈ C → c • f ∈ C := by
    intro c f hf
    rcases zmod2 c with rfl | rfl
    · rw [zero_smul]
      exact C.zero_mem
    · rw [one_smul]
      exact hf
  have hind : ∀ (α : Finset (Fin n)) (h : α.card = 4), ind α ∈ C := by
    intro α h
    show x * AE.mkQ n (AE.Wr.ofVec (ind α)) = AE.mkQ n (AE.Wr.ofVec (ind α)) * x
    rw [← zBar_eq]
    exact hx α h
  have hpair : ∀ i j : Fin n, i ≠ j →
      (fun m => (if m = i then (1 : ZMod 2) else 0) + (if m = j then 1 else 0)) ∈ C := by
    intro i j hij
    have hle := Finset.le_card_sdiff ({i, j} : Finset (Fin n)) Finset.univ
    rw [Finset.card_univ, Fintype.card_fin] at hle
    have hc2 : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
    obtain ⟨T, -, hTt, hT⟩ := Finset.exists_subsuperset_card_eq (n := 3)
      (Finset.empty_subset (Finset.univ \ ({i, j} : Finset (Fin n))))
      (by simp) (by omega)
    have hiT : i ∉ T := fun hi => (Finset.mem_sdiff.mp (hTt hi)).2 (by simp)
    have hjT : j ∉ T := fun hj => (Finset.mem_sdiff.mp (hTt hj)).2 (by simp)
    have hα : (insert i T).card = 4 := by rw [Finset.card_insert_of_notMem hiT, hT]
    have hβ : (insert j T).card = 4 := by rw [Finset.card_insert_of_notMem hjT, hT]
    have hsum : ind (insert i T) + ind (insert j T) =
        (fun m => (if m = i then (1 : ZMod 2) else 0) + (if m = j then 1 else 0)) := by
      funext m
      by_cases hmi : m = i <;> by_cases hmj : m = j <;> by_cases hmT : m ∈ T <;>
        simp [ind, Finset.mem_insert, hmi, hmj, hmT, hiT, hjT, hij, Ne.symm hij] <;> decide
    have h := C.add_mem (hind (insert i T) hα) (hind (insert j T) hβ)
    rw [hsum] at h
    exact h
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  have hdec : ∀ f : Fin n → ZMod 2, ∑ i, f i = 0 →
      f = ∑ k ∈ Finset.univ.erase i₀,
        f k • (fun m => (if m = k then (1 : ZMod 2) else 0) + (if m = i₀ then 1 else 0)) := by
    intro f hf
    have hsum : ∑ k ∈ Finset.univ.erase i₀, f k = f i₀ := by
      have h1 := Finset.add_sum_erase Finset.univ f (Finset.mem_univ i₀)
      rw [hf] at h1
      have h2 : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
      exact h2 _ _ h1
    funext m
    by_cases hm : m = i₀
    · subst hm
      simp [Finset.sum_apply, Finset.sum_mul, mul_add, Finset.sum_add_distrib, hsum]
    · simp [Finset.sum_apply, mul_add, Finset.sum_add_distrib, mul_ite, hm,
        Finset.sum_ite_eq', Finset.mem_erase]
  have hev : ∀ f : Fin n → ZMod 2, ∑ i, f i = 0 →
      x * AE.mkQ n (AE.Wr.ofVec f) = AE.mkQ n (AE.Wr.ofVec f) * x := by
    intro f hf
    have hfC : f ∈ C := by
      rw [hdec f hf]
      exact C.sum_mem fun k hk => hsmul _ _ (hpair k i₀ (Finset.ne_of_mem_erase hk))
    exact hfC
  obtain ⟨v, hv⟩ := AE.eq_vec_of_comm_vectors hn5 hev
  exact ⟨v, hv⟩

theorem conj_mem {P : Set (Subgroup G)} {a : G} (hperm : ∀ L ∈ P, conjSub a L ∈ P) :
    ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P := by
  intro y hy
  have hle : pSpan P ≤ (pSpan P).comap (MulAut.conj a).toMonoidHom := by
    apply pSpan_le
    intro L hL w hw
    exact le_pSpan (hperm L hL) (conj_mem_conjSub hw)
  exact hle hy

theorem center_le_ker {P : Set (Subgroup G)} {n : ℕ} (hn5 : 5 ≤ n) (I : AEIdent P n) :
    Subgroup.center (pSpan P) ≤ I.φ.ker := by
  intro z hz
  rw [MonoidHom.mem_ker]
  refine centralizer_eq_one hn5 (I.φ z) fun m hm => ?_
  rw [← I.range_eq] at hm
  obtain ⟨y, rfl⟩ := hm
  rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hz y).symm]

@[expose] def conjEquiv {P : Set (Subgroup G)} {a : G}
    (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P)
    (ha' : ∀ y ∈ pSpan P, a⁻¹ * y * a⁻¹⁻¹ ∈ pSpan P) : pSpan P ≃* pSpan P where
  toFun y := ⟨a * y * a⁻¹, ha y y.2⟩
  invFun y := ⟨a⁻¹ * y * a⁻¹⁻¹, ha' y y.2⟩
  left_inv y := by
    ext
    simp [mul_assoc]
  right_inv y := by
    ext
    simp [mul_assoc]
  map_mul' y z := by
    ext
    simp [mul_assoc]

theorem map_conjEquiv {P : Set (Subgroup G)} {a : G}
    (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P) (ha' : ∀ y ∈ pSpan P, a⁻¹ * y * a⁻¹⁻¹ ∈ pSpan P)
    (L : Subgroup G) :
    (L.subgroupOf (pSpan P)).map (conjEquiv ha ha').toMonoidHom =
      (conjSub a L).subgroupOf (pSpan P) := by
  ext w
  rw [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hy
    rw [mem_conjSub_iff]
    have e : a⁻¹ * ((conjEquiv ha ha').toMonoidHom y : G) * a = y := by
      show a⁻¹ * (a * (y : G) * a⁻¹) * a = y
      group
    rw [e]
    exact hy
  · intro hw
    rw [mem_conjSub_iff] at hw
    have hw' : a⁻¹ * (w : G) * a⁻¹⁻¹ ∈ L := by
      rw [inv_inv]
      exact hw
    refine ⟨⟨a⁻¹ * (w : G) * a⁻¹⁻¹, ha' w w.2⟩, Subgroup.mem_subgroupOf.mpr hw', ?_⟩
    apply Subtype.ext
    show a * (a⁻¹ * (w : G) * a⁻¹⁻¹) * a⁻¹ = w
    group

theorem exists_conj {P : Set (Subgroup G)} {n : ℕ}
    (hn5 : 5 ≤ n) (I : AEIdent P n) {a : G}
    (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P) (ha' : ∀ y ∈ pSpan P, a⁻¹ * y * a⁻¹⁻¹ ∈ pSpan P)
    (hperm : ∀ L ∈ P, conjSub a L ∈ P) :
    ∃ x : AE.AEQ n, ∀ (y : G) (hy : y ∈ pSpan P) (hy' : a * y * a⁻¹ ∈ pSpan P),
      I.φ ⟨a * y * a⁻¹, hy'⟩ = x * I.φ ⟨y, hy⟩ * x⁻¹ := by
  set c := conjEquiv ha ha' with hc_def
  have hZ := center_le_ker hn5 I
  obtain ⟨f, hf⟩ : ∃ f : ↥(pSpan P) →* ↥((AE.aeSub n).map (AE.mkQ n)),
      ∀ y, (f y : AE.AEQ n) = I.φ y :=
    ⟨I.φ.codRestrict _ fun y => by rw [← I.range_eq]; exact ⟨y, rfl⟩, fun _ => rfl⟩
  have hfs : Function.Surjective f := by
    rintro ⟨m, hm⟩
    rw [← I.range_eq] at hm
    obtain ⟨y, rfl⟩ := hm
    exact ⟨y, Subtype.ext (hf y)⟩
  have hfk : f.ker = Subgroup.center ↥(pSpan P) := by
    refine le_antisymm (fun y hy => I.ker_le ?_) fun y hy => ?_
    · rw [MonoidHom.mem_ker, ← hf, MonoidHom.mem_ker.mp hy]
      rfl
    · exact MonoidHom.mem_ker.mpr (Subtype.ext ((hf y).trans (MonoidHom.mem_ker.mp (hZ hy))))
  have hck : f.ker.map c.toMonoidHom = f.ker := by
    rw [hfk]
    exact Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : (Subgroup.center ↥(pSpan P)).Characteristic) c
  obtain ⟨β, hβ⟩ : ∃ β : MulAut ↥((AE.aeSub n).map (AE.mkQ n)), ∀ y, β (f y) = f (c y) := by
    refine ⟨((QuotientGroup.quotientKerEquivOfSurjective f hfs).symm.trans
      (QuotientGroup.congr f.ker f.ker c hck)).trans
        (QuotientGroup.quotientKerEquivOfSurjective f hfs), fun y => ?_⟩
    have h1 : (QuotientGroup.quotientKerEquivOfSurjective f hfs).symm (f y) =
        (y : ↥(pSpan P) ⧸ f.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1]
    rfl
  have hsub : ∀ H : Subgroup ↥(pSpan P),
      (H.map I.φ).subgroupOf ((AE.aeSub n).map (AE.mkQ n)) = H.map f := by
    intro H
    ext m
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
    constructor
    · rintro ⟨y, hy, hym⟩
      exact ⟨y, hy, Subtype.ext ((hf y).trans hym)⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, (hf y).symm⟩
  have hcomp : β.toMonoidHom.comp f = f.comp c.toMonoidHom := MonoidHom.ext hβ
  obtain ⟨x, hx⟩ := TC.Thin.model117At_of_five_le hn5 β fun α hα b => by
    obtain ⟨L, hL, hLe⟩ := I.label_surj α hα b
    obtain ⟨α', hα', b', hL'e⟩ := I.label (conjSub a L) (hperm L hL)
    refine ⟨α', hα', b', ?_⟩
    rw [← hLe, ← hL'e, hsub, hsub, Subgroup.map_map, hcomp, ← Subgroup.map_map,
      map_conjEquiv ha ha']
  refine ⟨x, fun y hy hy' => ?_⟩
  have h1 : I.φ ⟨a * y * a⁻¹, hy'⟩ = (f (c ⟨y, hy⟩) : AE.AEQ n) := (hf _).symm
  rw [h1, ← hβ, hx, hf]

@[expose] def IsConj {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) (a : G) (x : AE.AEQ n) :
    Prop :=
  ∀ (y : G) (hy : y ∈ pSpan P) (hy' : a * y * a⁻¹ ∈ pSpan P),
    I.φ ⟨a * y * a⁻¹, hy'⟩ = x * I.φ ⟨y, hy⟩ * x⁻¹

theorem eq_of_isConj {P : Set (Subgroup G)} {n : ℕ} (hn5 : 5 ≤ n) (I : AEIdent P n)
    {a : G} (ha : ∀ y ∈ pSpan P, a * y * a⁻¹ ∈ pSpan P) {x x' : AE.AEQ n}
    (h : IsConj I a x) (h' : IsConj I a x') : x = x' := by
  have hc : x'⁻¹ * x = 1 := by
    apply centralizer_eq_one hn5
    intro g hg
    have hg' : g ∈ I.φ.range := by
      rw [I.range_eq]
      exact hg
    obtain ⟨w, rfl⟩ := MonoidHom.mem_range.mp hg'
    have h1 : I.φ ⟨a * w * a⁻¹, ha _ w.2⟩ = x * I.φ w * x⁻¹ := h w.1 w.2 (ha _ w.2)
    have h2 : I.φ ⟨a * w * a⁻¹, ha _ w.2⟩ = x' * I.φ w * x'⁻¹ := h' w.1 w.2 (ha _ w.2)
    have e : x * I.φ w * x⁻¹ = x' * I.φ w * x'⁻¹ := h1.symm.trans h2
    calc x'⁻¹ * x * I.φ w = x'⁻¹ * (x * I.φ w * x⁻¹) * x := by group
      _ = x'⁻¹ * (x' * I.φ w * x'⁻¹) * x := by rw [e]
      _ = I.φ w * (x'⁻¹ * x) := by group
  exact (inv_mul_eq_one.mp hc).symm

theorem one_isConj {P : Set (Subgroup G)} {n : ℕ} (I : AEIdent P n) :
    IsConj I 1 (1 : AE.AEQ n) := by
  intro y hy hy'
  have e : (⟨1 * y * 1⁻¹, hy'⟩ : pSpan P) = ⟨y, hy⟩ := Subtype.ext (by simp)
  rw [e]
  simp


end Vec

end CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6c
