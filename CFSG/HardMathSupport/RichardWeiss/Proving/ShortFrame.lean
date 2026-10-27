module

public import CFSG.HardMathSupport.RichardWeiss.Proving.ShortTwist
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.Frame
public import CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0.PairPerm

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.RankThree.PartTwo CFSG.QuasithinUnique CFSG.HardMathSupport.Cooperstein.Coordinator
  CFSG.HardMathSupport.Cooperstein.AlternatingGeometry Equiv Equiv.Perm
open scoped commutatorElement

variable {G : Type} [Group G] {Q L V S : Subgroup G}

@[expose] def CQ (Q L : Subgroup G) : Subgroup ↥Q :=
  (Q ⊓ Subgroup.centralizer (L : Set G)).subgroupOf Q

theorem mem_CQ {q : ↥Q} : q ∈ CQ Q L ↔ ∀ l ∈ L, (l : G) * q = q * l := by
  show (q : G) ∈ Q ⊓ Subgroup.centralizer (L : Set G) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact ⟨fun h => h.2, fun h => ⟨q.2, h⟩⟩

theorem CQ_normal (hQN : ∀ q ∈ Q, ∀ l ∈ L, q * l * q⁻¹ ∈ L) : (CQ Q L).Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [mem_CQ] at hn ⊢
  intro l hl
  have hl' : (g : G)⁻¹ * l * (g : G) ∈ L := by
    have := hQN (g : G)⁻¹ (Q.inv_mem g.2) l hl
    simpa using this
  have h := hn _ hl'
  show (l : G) * ((g : G) * (n : G) * (g : G)⁻¹) = ((g : G) * (n : G) * (g : G)⁻¹) * l
  calc (l : G) * ((g : G) * (n : G) * (g : G)⁻¹)
      = (g : G) * (((g : G)⁻¹ * l * (g : G)) * (n : G)) * (g : G)⁻¹ := by group
    _ = (g : G) * ((n : G) * ((g : G)⁻¹ * l * (g : G))) * (g : G)⁻¹ := by rw [h]
    _ = ((g : G) * (n : G) * (g : G)⁻¹) * l := by group

class ShortCtx (Q L : Subgroup G) : Prop where
  qn : ∀ q ∈ Q, ∀ l ∈ L, q * l * q⁻¹ ∈ L
  qc : ∀ x y : ↥Q, ∀ l ∈ L, (l : G) * ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) =
    ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) * l

theorem ShortData.shortCtx (D : ShortData Q L V S) : ShortCtx Q L where
  qn q hq l hl := D.hML q (D.hQM hq) l hl
  qc x y l hl := by
    have h := D.conj_commutator (x := (x : G)) (y := (y : G)) x.2 y.2 hl
    have : (l : G) * ⁅(x : G), (y : G)⁆ = ⁅(x : G), (y : G)⁆ * l := by
      rw [mul_inv_eq_iff_eq_mul] at h; exact h
    simpa [commutatorElement_def] using this

instance [ShortCtx Q L] : (CQ Q L).Normal := CQ_normal ShortCtx.qn

instance [ShortCtx Q L] : CommGroup (↥Q ⧸ CQ Q L) :=
  { (inferInstance : Group (↥Q ⧸ CQ Q L)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with | H x => ?_
      induction b using QuotientGroup.induction_on with | H y => ?_
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, mem_CQ]
      intro l hl
      have h := ShortCtx.qc (Q := Q) (L := L) y⁻¹ x⁻¹ l hl
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_inv_rev, mul_assoc] at h ⊢
      exact h }

section Action

variable [ShortCtx Q L]

@[expose] def conjQ (hMQ : ∀ m ∈ L ⊔ S, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q) (m : ↥(L ⊔ S)) : ↥Q →* ↥Q where
  toFun q := ⟨(m : G) * q * (m : G)⁻¹, hMQ m m.2 q q.2⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp [mul_assoc]

theorem conjQ_mem_CQ (hMQ : ∀ m ∈ L ⊔ S, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q)
    (hML : ∀ m ∈ L ⊔ S, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (m : ↥(L ⊔ S)) {c : ↥Q} (hc : c ∈ CQ Q L) :
    conjQ hMQ m c ∈ CQ Q L := by
  rw [mem_CQ] at hc ⊢
  intro l hl
  have hl' : (m : G)⁻¹ * l * (m : G) ∈ L := by
    have := hML (m : G)⁻¹ (Subgroup.inv_mem _ m.2) l hl
    simpa using this
  have h := hc _ hl'
  show (l : G) * ((m : G) * (c : G) * (m : G)⁻¹) = ((m : G) * (c : G) * (m : G)⁻¹) * l
  calc (l : G) * ((m : G) * (c : G) * (m : G)⁻¹)
      = (m : G) * (((m : G)⁻¹ * l * (m : G)) * (c : G)) * (m : G)⁻¹ := by group
    _ = (m : G) * ((c : G) * ((m : G)⁻¹ * l * (m : G))) * (m : G)⁻¹ := by rw [h]
    _ = ((m : G) * (c : G) * (m : G)⁻¹) * l := by group

@[expose] noncomputable def convQ (hMQ : ∀ m ∈ L ⊔ S, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q)
    (hML : ∀ m ∈ L ⊔ S, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (m : ↥(L ⊔ S)) :
    (↥Q ⧸ CQ Q L) →* (↥Q ⧸ CQ Q L) :=
  QuotientGroup.map (CQ Q L) (CQ Q L) (conjQ hMQ m) (fun _ hc => conjQ_mem_CQ hMQ hML m hc)

theorem convQ_mk (hMQ : ∀ m ∈ L ⊔ S, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q)
    (hML : ∀ m ∈ L ⊔ S, ∀ l ∈ L, m * l * m⁻¹ ∈ L) (m : ↥(L ⊔ S)) (q : ↥Q) :
    convQ hMQ hML m (QuotientGroup.mk q) = QuotientGroup.mk (conjQ hMQ m q) := rfl

@[expose] noncomputable def rhoQ (hMQ : ∀ m ∈ L ⊔ S, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q)
    (hML : ∀ m ∈ L ⊔ S, ∀ l ∈ L, m * l * m⁻¹ ∈ L) :
    ↥(L ⊔ S) →* AddMonoid.End (Additive (↥Q ⧸ CQ Q L)) where
  toFun m := AddMonoidHom.mk' (fun v : Additive (↥Q ⧸ CQ Q L) =>
    Additive.ofMul (convQ hMQ hML m (Additive.toMul v))) (fun a b => by simp)
  map_one' := by
    apply AddMonoidHom.ext
    intro v
    apply Additive.toMul.injective
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    show convQ hMQ hML 1 (Additive.toMul v) = Additive.toMul v
    rw [← hx, convQ_mk]
    congr 1
    apply Subtype.ext
    simp [conjQ]
  map_mul' m n := by
    apply AddMonoidHom.ext
    intro v
    apply Additive.toMul.injective
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    show convQ hMQ hML (m * n) (Additive.toMul v) =
      convQ hMQ hML m (convQ hMQ hML n (Additive.toMul v))
    rw [← hx, convQ_mk, convQ_mk, convQ_mk]
    congr 1
    apply Subtype.ext
    simp only [conjQ, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_mul, mul_inv_rev, mul_assoc]

@[expose] def UW (Q V L : Subgroup G) [ShortCtx Q L] : AddSubgroup (Additive (↥Q ⧸ CQ Q L)) :=
  Subgroup.toAddSubgroup ((⁅V, L⁆.subgroupOf Q).map (QuotientGroup.mk' (CQ Q L)))

theorem mem_UW [ShortCtx Q L] {x : Additive (↥Q ⧸ CQ Q L)} :
    x ∈ UW Q V L ↔ ∃ u : ↥Q, (u : G) ∈ ⁅V, L⁆ ∧ QuotientGroup.mk u = Additive.toMul x := by
  show Additive.toMul x ∈ (⁅V, L⁆.subgroupOf Q).map (QuotientGroup.mk' (CQ Q L)) ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨u, Subgroup.mem_subgroupOf.1 hu, h⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u, Subgroup.mem_subgroupOf.2 hu, h⟩

end Action

section Pi

variable {N : ℕ} [ShortCtx Q L] {π : ↥⁅V, L⁆ →* Multiplicative (altHeart N)}
  {θ : ↥(L ⊔ S) →* Perm (Fin N)}

theorem piA_eq_of_mk_eq (H : ShortSection Q L V S π θ) {u u' : ↥Q} (hu : (u : G) ∈ ⁅V, L⁆)
    (hu' : (u' : G) ∈ ⁅V, L⁆)
    (h : (QuotientGroup.mk u : ↥Q ⧸ CQ Q L) = QuotientGroup.mk u') :
    piA π (u : G) = piA π (u' : G) := by
  have h1 := QuotientGroup.eq.1 h
  rw [mem_CQ] at h1
  have hU : (u : G)⁻¹ * (u' : G) ∈ ⁅V, L⁆ := ⁅V, L⁆.mul_mem (⁅V, L⁆.inv_mem hu) hu'
  have hc : (u : G)⁻¹ * (u' : G) ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have := h1 l hl
    simpa using this
  have hker : (⟨(u : G)⁻¹ * (u' : G), hU⟩ : ↥⁅V, L⁆) ∈ π.ker := by
    rw [H.hπker, Subgroup.mem_subgroupOf]
    exact ⟨hU, hc⟩
  have h0 : piA π ((u : G)⁻¹ * (u' : G)) = 0 := by
    rw [piA_of_mem hU]
    have : π ⟨(u : G)⁻¹ * (u' : G), hU⟩ = 1 := hker
    rw [this]; rfl
  have := piA_mul (π := π) hu hU
  rw [mul_inv_cancel_left, h0, add_zero] at this
  exact this.symm

@[expose] noncomputable def piW (H : ShortSection Q L V S π θ) : ↥(UW Q V L) →+ altHeart N where
  toFun x := piA π (((mem_UW.1 x.2).choose : ↥Q) : G)
  map_zero' := by
    have hc := (mem_UW.1 (0 : ↥(UW Q V L)).2).choose_spec
    have h1 : (QuotientGroup.mk (1 : ↥Q) : ↥Q ⧸ CQ Q L) =
        Additive.toMul ((0 : ↥(UW Q V L)) : Additive (↥Q ⧸ CQ Q L)) := rfl
    have := piA_eq_of_mk_eq H hc.1 (Subgroup.one_mem _ : ((1 : ↥Q) : G) ∈ ⁅V, L⁆)
      (hc.2.trans h1.symm)
    rw [this]
    exact piA_one
  map_add' x y := by
    have hx := (mem_UW.1 x.2).choose_spec
    have hy := (mem_UW.1 y.2).choose_spec
    have hxy := (mem_UW.1 (x + y).2).choose_spec
    set ux := (mem_UW.1 x.2).choose
    set uy := (mem_UW.1 y.2).choose
    set uxy := (mem_UW.1 (x + y).2).choose
    have hmem : ((ux * uy : ↥Q) : G) ∈ ⁅V, L⁆ := ⁅V, L⁆.mul_mem hx.1 hy.1
    have hmk : (QuotientGroup.mk (ux * uy) : ↥Q ⧸ CQ Q L) =
        Additive.toMul (((x + y : ↥(UW Q V L)) : Additive (↥Q ⧸ CQ Q L))) := by
      rw [QuotientGroup.mk_mul, hx.2, hy.2]; rfl
    have := piA_eq_of_mk_eq H hxy.1 hmem (hxy.2.trans hmk.symm)
    rw [this]
    exact piA_mul hx.1 hy.1

theorem piW_eq (H : ShortSection Q L V S π θ) (x : ↥(UW Q V L)) {u : ↥Q}
    (hu : (u : G) ∈ ⁅V, L⁆) (h : (QuotientGroup.mk u : ↥Q ⧸ CQ Q L) =
      Additive.toMul (x : Additive (↥Q ⧸ CQ Q L))) : piW H x = piA π (u : G) := by
  have hc := (mem_UW.1 x.2).choose_spec
  exact piA_eq_of_mk_eq H hc.1 hu (hc.2.trans h.symm)

end Pi

section FrameFields

open CFSG.HardMathSupport.RichardWeiss.ExceptionalClosure.E0

variable {N : ℕ} [ShortCtx Q L] {π : ↥⁅V, L⁆ →* Multiplicative (altHeart N)}
  {θ : ↥(L ⊔ S) →* Perm (Fin N)}

theorem toMul_rhoQ (D : ShortData Q L V S) (m : ↥(L ⊔ S)) (v : Additive (↥Q ⧸ CQ Q L)) :
    Additive.toMul (rhoQ D.hMQ D.hML m v) = convQ D.hMQ D.hML m (Additive.toMul v) := rfl

theorem piW_zero_iff (D : ShortData Q L V S) (H : ShortSection Q L V S π θ)
    (x : ↥(UW Q V L)) (hx : piW H x = 0) : (x : Additive (↥Q ⧸ CQ Q L)) = 0 := by
  obtain ⟨u, hu, hmk⟩ := mem_UW.1 x.2
  rw [piW_eq H x hu hmk] at hx
  rw [piA_of_mem hu] at hx
  have h1 : π ⟨(u : G), hu⟩ = 1 := by
    apply Multiplicative.toAdd.injective
    exact hx
  have : (⟨(u : G), hu⟩ : ↥⁅V, L⁆) ∈ π.ker := h1
  rw [H.hπker, Subgroup.mem_subgroupOf] at this
  have hc : u ∈ CQ Q L := by
    rw [mem_CQ]
    intro l hl
    have := Subgroup.mem_centralizer_iff.1 this.2 l hl
    exact this
  apply Additive.toMul.injective
  rw [← hmk]
  exact (QuotientGroup.eq_one_iff u).2 hc

theorem piFrame_of_short (hN : 6 ≤ N) (hev : Even N) (D : ShortData Q L V S)
    (H : ShortSection Q L V S π θ) :
    PiFrame (W := Additive (↥Q ⧸ CQ Q L)) θ (rhoQ D.hMQ D.hML) (UW Q V L) (piW H)
      (L.subgroupOf (L ⊔ S)) (S.subgroupOf (L ⊔ S)) := by
  have hUV := D.commutator_le
  have hUQ : ⁅V, L⁆ ≤ Q := hUV.trans D.hVQ
  have htwo : ∀ w : Additive (↥Q ⧸ CQ Q L), w + w = 0 := by
    intro w
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    apply Additive.toMul.injective
    show Additive.toMul w * Additive.toMul w = 1
    rw [← hq, ← QuotientGroup.mk_mul]
    refine (QuotientGroup.eq_one_iff _).2 (mem_CQ.2 fun l hl => ?_)
    have h := D.conj_sq q.2 hl
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h
  have hker : ∀ m : ↥(L ⊔ S), θ m = 1 → rhoQ D.hMQ D.hML m = 1 := by
    intro m hm
    apply AddMonoidHom.ext
    intro v
    apply Additive.toMul.injective
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul v)
    show convQ D.hMQ D.hML m (Additive.toMul v) = Additive.toMul v
    rw [← hq, convQ_mk]
    refine QuotientGroup.eq.2 (mem_CQ.2 fun l hl => ?_)
    have hc := Subgroup.mem_centralizer_iff.1 (H.hker m hm ((q : G)⁻¹) (Q.inv_mem q.2)).2 l hl
    have e : ((((conjQ D.hMQ m q)⁻¹ * q : ↥Q)) : G) = ⁅(m : G), (q : G)⁻¹⁆ := by
      simp [conjQ, commutatorElement_def, mul_assoc]
    rw [e]
    exact hc
  have hstable : ∀ (m : ↥(L ⊔ S)), ∀ u ∈ UW Q V L, rhoQ D.hMQ D.hML m u ∈ UW Q V L := by
    intro m u hu
    obtain ⟨q, hqU, hq⟩ := mem_UW.1 hu
    refine mem_UW.2 ⟨conjQ D.hMQ m q, D.conj_mem_U H m.2 hqU, ?_⟩
    rw [toMul_rhoQ D, ← hq, convQ_mk]
  have hrho : ∀ (m : ↥(L ⊔ S)) (q : ↥Q), Additive.toMul (rhoQ D.hMQ D.hML m
      (Additive.ofMul (QuotientGroup.mk q))) = QuotientGroup.mk (conjQ D.hMQ m q) := fun m q => rfl
  refine ⟨htwo, hker, hstable, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro m u
    obtain ⟨q, hqU, hq⟩ := mem_UW.1 u.2
    have hconj : ((conjQ D.hMQ m q : ↥Q) : G) ∈ ⁅V, L⁆ := D.conj_mem_U H m.2 hqU
    have h1 : piW H u = piA π (q : G) := piW_eq H u hqU hq
    have h2 : piW H ⟨rhoQ D.hMQ D.hML m u, hstable m u u.2⟩ = piA π ((conjQ D.hMQ m q : ↥Q) : G) :=
      piW_eq H _ hconj (by rw [toMul_rhoQ D, ← hq, convQ_mk])
    rw [h2, h1]
    have := piA_conj H.hequiv m.2 hqU hconj
    rw [thetaA_of_mem m.2] at this
    exact this
  ·
    intro v
    obtain ⟨u, hu⟩ := H.hπ (Multiplicative.ofAdd v)
    let q : ↥Q := ⟨(u : G), hUQ u.2⟩
    let x : ↥(UW Q V L) := ⟨Additive.ofMul (QuotientGroup.mk q), mem_UW.2 ⟨q, u.2, rfl⟩⟩
    refine ⟨x, ?_⟩
    rw [piW_eq H x (u := q) u.2 rfl, piA_of_mem u.2]
    have : (⟨(q : G), u.2⟩ : ↥⁅V, L⁆) = u := rfl
    rw [this, hu]; rfl
  ·
    intro σ hσ
    obtain ⟨l, hl⟩ := H.hAθ σ hσ
    exact ⟨⟨(l : G), Subgroup.mem_sup_left l.2⟩, Subgroup.mem_subgroupOf.2 l.2, hl⟩
  ·
    intro l hl w
    have hl' : (l : G) ∈ L := Subgroup.mem_subgroupOf.1 hl
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    have hcq : (l : G) * q * (l : G)⁻¹ * (q : G)⁻¹ ∈ Q :=
      Q.mul_mem (D.hMQ l l.2 q q.2) (Q.inv_mem q.2)
    refine mem_UW.2 ⟨⟨_, hcq⟩, D.comm_mem_U q.2 hl', ?_⟩
    rw [toMul_sub, toMul_rhoQ D, ← hq, convQ_mk]
    show (QuotientGroup.mk _ : ↥Q ⧸ CQ Q L) = QuotientGroup.mk (conjQ D.hMQ l q) / QuotientGroup.mk q
    rw [div_eq_mul_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    congr 1
  ·
    intro s hs w
    have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
    obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
    obtain ⟨u, hu, c, hc, hsq⟩ := D.short_twist H hN hev q.2 s.2
    have hcq : (s : G) * q * (s : G)⁻¹ * (q : G)⁻¹ ∈ Q :=
      Q.mul_mem (D.hMQ s s.2 q q.2) (Q.inv_mem q.2)
    have huQ : u ∈ Q := (D.commutator_le.trans D.hVQ) hu
    refine mem_UW.2 ⟨⟨u, huQ⟩, hu, ?_⟩
    rw [toMul_sub, toMul_rhoQ D, ← hq, convQ_mk]
    rw [div_eq_mul_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
    refine QuotientGroup.eq.2 (mem_CQ.2 fun l hl => ?_)
    have hcomm := Subgroup.mem_centralizer_iff.1 hc.2
    have e : (conjQ D.hMQ s q * q⁻¹ : ↥Q) = ⟨(s : G) * q * (s : G)⁻¹ * (q : G)⁻¹, hcq⟩ := rfl
    have hsq' : (s : G) * q * (s : G)⁻¹ * (q : G)⁻¹ = u * c := hsq
    rw [e]
    show (l : G) * ((u : G)⁻¹ * ((s : G) * q * (s : G)⁻¹ * (q : G)⁻¹)) =
      ((u : G)⁻¹ * ((s : G) * q * (s : G)⁻¹ * (q : G)⁻¹)) * l
    rw [hsq']
    have : (u : G)⁻¹ * (u * c) = c := by group
    rw [this]
    exact hcomm l hl
  ·
    intro s hs u hu
    have h0 := piW_zero_iff D H u hu
    rw [h0, map_zero]

@[expose] def YW (Q L S : Subgroup G) [ShortCtx Q L] : AddSubgroup (Additive (↥Q ⧸ CQ Q L)) :=
  Subgroup.toAddSubgroup ((⁅S, S⁆.subgroupOf Q).map (QuotientGroup.mk' (CQ Q L)))

theorem mem_YW [ShortCtx Q L] {x : Additive (↥Q ⧸ CQ Q L)} :
    x ∈ YW Q L S ↔ ∃ u : ↥Q, (u : G) ∈ ⁅S, S⁆ ∧ QuotientGroup.mk u = Additive.toMul x := by
  show Additive.toMul x ∈ (⁅S, S⁆.subgroupOf Q).map (QuotientGroup.mk' (CQ Q L)) ↔ _
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨u, hu, h⟩
    exact ⟨u, Subgroup.mem_subgroupOf.1 hu, h⟩
  · rintro ⟨u, hu, h⟩
    exact ⟨u, Subgroup.mem_subgroupOf.2 hu, h⟩

theorem e0Frame_of_short (hN : 10 ≤ N) (D : ShortData Q L V S) (H : ShortSection Q L V S π θ)
    {P : Subgroup (Perm (Fin N))} {ω : Perm (Fin N)} {Δ₀ : Finset (Fin N)}
    (hshape : E0Shape P ω Δ₀)
    (hθS : ∀ m : ↥(L ⊔ S), θ m = 1 → (m : G) ∈ S)
    (hθ : (S.subgroupOf (L ⊔ S)).map θ =
      P ⊔ Subgroup.closure {τ | ∃ x, x ∉ Δ₀ ∧ τ = swap x (ω x)}) :
    E0Frame (W := Additive (↥Q ⧸ CQ Q L)) θ (rhoQ D.hMQ D.hML) (UW Q V L) (piW H)
      (L.subgroupOf (L ⊔ S)) (S.subgroupOf (L ⊔ S)) P ω Δ₀ (YW Q L S) := by
  have hev : Even N := hshape.even_card
  refine ⟨piFrame_of_short (by omega) hev D H, hshape, hN, hev, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ
    have : σ ∈ (S.subgroupOf (L ⊔ S)).map θ ↔ σ ∈ E0grp P ω Δ₀ := by rw [hθ]; rfl
    rw [← this, Subgroup.mem_map]
  · intro m hm
    exact Subgroup.mem_subgroupOf.2 (hθS m hm)
  · intro l hl u hu
    have h0 := piW_zero_iff D H u hu
    rw [h0, map_zero]
  · have hold : ∀ s ∈ S.subgroupOf (L ⊔ S), ∀ w : Additive (↥Q ⧸ CQ Q L),
        rhoQ D.hMQ D.hML s w - w ∈ YW Q L S := by
      intro s hs w
      have hs' : (s : G) ∈ S := Subgroup.mem_subgroupOf.1 hs
      obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (Additive.toMul w)
      have hcq : (s : G) * q * (s : G)⁻¹ * (q : G)⁻¹ ∈ Q :=
        Q.mul_mem (D.hMQ s s.2 q q.2) (Q.inv_mem q.2)
      refine mem_YW.2 ⟨⟨_, hcq⟩, Subgroup.commutator_mem_commutator hs' (D.hQS q.2), ?_⟩
      rw [toMul_sub, toMul_rhoQ D, ← hq, convQ_mk]
      show (QuotientGroup.mk _ : ↥Q ⧸ CQ Q L) = QuotientGroup.mk (conjQ D.hMQ s q) / QuotientGroup.mk q
      rw [div_eq_mul_inv, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
      congr 1
    exact fun s hs u => hold s hs u
  · intro m hm y hy
    obtain ⟨q, hqS, hq⟩ := mem_YW.1 hy
    have hm' : ∀ s ∈ S, (m : G) * s * (m : G)⁻¹ ∈ S := fun s hs => by
      have := hm ⟨s, Subgroup.mem_sup_right hs⟩ (Subgroup.mem_subgroupOf.2 hs)
      exact Subgroup.mem_subgroupOf.1 this
    refine mem_YW.2 ⟨conjQ D.hMQ m q, conj_mem_commutator_VL hm' hm' hqS, ?_⟩
    rw [toMul_rhoQ D, ← hq, convQ_mk]

end FrameFields

end CFSG.HardMathSupport.RichardWeiss.Proving
