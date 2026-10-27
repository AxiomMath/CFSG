module

public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma129W

public section

namespace CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129W3

open CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129W

section Regular

variable {Y : Type*} [Group Y] {Q : Type*} [Group Q] [Fintype Q] [DecidableEq Q]

private def conjEmb (ρ : Q →* Y) (K : Subgroup Y) (x : Q) : K →* Y :=
  (MulAut.conj (ρ x)).toMonoidHom.comp K.subtype

private theorem conjEmb_apply (ρ : Q →* Y) (K : Subgroup Y) (x : Q) (k : K) :
    conjEmb ρ K x k = ρ x * k * (ρ x)⁻¹ := rfl

private theorem conjEmb_injective (ρ : Q →* Y) (K : Subgroup Y) (x : Q) :
    Function.Injective (conjEmb ρ K x) :=
  (MulAut.conj (ρ x)).injective.comp K.subtype_injective

private abbrev ConjComm (ρ : Q →* Y) (K : Subgroup Y) : Prop :=
  Pairwise fun x y : Q => ∀ k l : K, Commute (conjEmb ρ K x k) (conjEmb ρ K y l)

variable {ρ : Q →* Y} {K : Subgroup Y}

private def prodHom (hc : ConjComm ρ K) : (Q → K) →* Y :=
  MonoidHom.noncommPiCoprod (conjEmb ρ K) hc

private theorem prodHom_mulSingle (hc : ConjComm ρ K) (x : Q) (k : K) :
    prodHom hc (Pi.mulSingle x k) = ρ x * k * (ρ x)⁻¹ :=
  MonoidHom.noncommPiCoprod_mulSingle (conjEmb ρ K) x k

private def shiftHom (K : Type*) [Group K] (q : Q) : (Q → K) →* (Q → K) where
  toFun f x := f (q⁻¹ * x)
  map_one' := rfl
  map_mul' _ _ := rfl

private theorem shiftHom_mulSingle {K : Type*} [Group K] (q x : Q) (k : K) :
    shiftHom K q (Pi.mulSingle x k) = Pi.mulSingle (q * x) k := by
  funext y
  simp only [shiftHom, MonoidHom.coe_mk, OneHom.coe_mk, Pi.mulSingle_apply, inv_mul_eq_iff_eq_mul]

private theorem prodHom_shift (hc : ConjComm ρ K) (q : Q) (f : Q → K) :
    prodHom hc (fun x => f (q⁻¹ * x)) = ρ q * prodHom hc f * (ρ q)⁻¹ := by
  have key : (prodHom hc).comp (shiftHom K q) =
      (MulAut.conj (ρ q)).toMonoidHom.comp (prodHom hc) := by
    refine MonoidHom.pi_ext fun x k => ?_
    simp only [MonoidHom.coe_comp, Function.comp_apply, shiftHom_mulSingle, prodHom_mulSingle,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul]
    group
  exact DFunLike.congr_fun key f

private theorem prodHom_range (hc : ConjComm ρ K) :
    (prodHom hc).range = ⨆ x : Q, (conjEmb ρ K x).range :=
  MonoidHom.noncommPiCoprod_range (conjEmb ρ K)

private theorem prodHom_injective (hK : ∀ z ∈ K, (∀ y ∈ K, z * y = y * z) → z = 1)
    (hc : ConjComm ρ K) : Function.Injective (prodHom hc) := by
  refine MonoidHom.injective_noncommPiCoprod_of_iSupIndep (conjEmb ρ K) ?_ (conjEmb_injective ρ K)
  intro x
  rw [Subgroup.disjoint_def]
  rintro z ⟨k₀, rfl⟩ hz
  have hle : (⨆ y, ⨆ (_ : y ≠ x), (conjEmb ρ K y).range) ≤
      Subgroup.centralizer ((conjEmb ρ K x).range : Set Y) := by
    refine iSup₂_le fun y hy => ?_
    rintro _ ⟨l, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨k, rfl⟩
    exact (hc hy l k).symm.eq
  have hz' := Subgroup.mem_centralizer_iff.1 (hle hz)
  have hk₀ : k₀ = 1 := by
    refine Subtype.ext (hK k₀ k₀.2 fun y hy => ?_)
    have h := hz' (conjEmb ρ K x ⟨y, hy⟩) ⟨⟨y, hy⟩, rfl⟩
    rw [← map_mul, ← map_mul] at h
    exact congrArg Subtype.val (conjEmb_injective ρ K x h).symm
  rw [hk₀, map_one]

private def diagHom (hc : ConjComm ρ K) : K →* Y :=
  (prodHom hc).comp (Pi.constMonoidHom Q K)

private theorem diagHom_apply (hc : ConjComm ρ K) (x : K) :
    diagHom hc x = prodHom hc (fun _ => x) := rfl

private theorem diagHom_injective (hK : ∀ z ∈ K, (∀ y ∈ K, z * y = y * z) → z = 1)
    (hc : ConjComm ρ K) : Function.Injective (diagHom hc) := by
  intro x y h
  rw [diagHom_apply, diagHom_apply] at h
  exact congrFun (prodHom_injective hK hc h) 1

private theorem diagHom_commute (hc : ConjComm ρ K) (x : K) (q : Q) :
    diagHom hc x * ρ q = ρ q * diagHom hc x := by
  have h : prodHom hc (fun _ => x) = ρ q * prodHom hc (fun _ => x) * (ρ q)⁻¹ :=
    prodHom_shift hc q (fun _ => x)
  rw [diagHom_apply]
  calc prodHom hc (fun _ => x) * ρ q
      = (ρ q * prodHom hc (fun _ => x) * (ρ q)⁻¹) * ρ q := by rw [← h]
    _ = ρ q * prodHom hc (fun _ => x) := by group

private theorem prodHom_mulSingle_one (hc : ConjComm ρ K) (k : K) :
    prodHom hc (Pi.mulSingle 1 k) = (k : Y) := by
  rw [prodHom_mulSingle]
  simp

private theorem diagHom_conj (hc : ConjComm ρ K) (x y : K) :
    diagHom hc x * (y : Y) * (diagHom hc x)⁻¹ = (x : Y) * (y : Y) * (x : Y)⁻¹ := by
  have h : (fun _ : Q => x) * Pi.mulSingle 1 y * (fun _ : Q => x)⁻¹ =
      Pi.mulSingle 1 (x * y * x⁻¹) := by
    funext z
    by_cases hz : z = 1
    · subst hz
      simp
    · simp [Pi.mulSingle_eq_of_ne hz]
  have h' := congrArg (prodHom hc) h
  simp only [map_mul, map_inv, prodHom_mulSingle_one] at h'
  calc diagHom hc x * (y : Y) * (diagHom hc x)⁻¹ = ((x * y * x⁻¹ : K) : Y) := h'
    _ = (x : Y) * (y : Y) * (x : Y)⁻¹ := rfl

private theorem exists_const_of_commute (hK : ∀ z ∈ K, (∀ y ∈ K, z * y = y * z) → z = 1)
    (hc : ConjComm ρ K) {q : Q} (hq : ∀ y : Q, ∃ n : ℕ, y = q ^ n) {l : Q → K}
    (h : prodHom hc l * ρ q = ρ q * prodHom hc l) : ∃ x : K, l = fun _ => x := by
  have h1 : prodHom hc (fun x => l (q⁻¹ * x)) = prodHom hc l := by
    rw [prodHom_shift hc q l, ← h, mul_inv_cancel_right]
  have h2 : ∀ y, l (q⁻¹ * y) = l y := fun y => congrFun (prodHom_injective hK hc h1) y
  have h3 : ∀ n : ℕ, l (q ^ n) = l 1 := by
    intro n
    induction n with
    | zero => rw [pow_zero]
    | succ n ih =>
      calc l (q ^ (n + 1)) = l (q⁻¹ * q ^ (n + 1)) := (h2 _).symm
        _ = l (q ^ n) := by rw [pow_succ', inv_mul_cancel_left]
        _ = l 1 := ih
  refine ⟨l 1, funext fun y => ?_⟩
  obtain ⟨n, rfl⟩ := hq y
  exact h3 n

private noncomputable def projHom (hc : ConjComm ρ K) (hinj : Function.Injective (prodHom hc))
    {B : Subgroup Y} (hB : (prodHom hc).range = B) : B →* K :=
  (Pi.evalMonoidHom (fun _ : Q => ↥K) 1).comp
    ((MonoidHom.ofInjective hinj).symm.toMonoidHom.comp (Subgroup.inclusion hB.ge))

private theorem projHom_eq (hc : ConjComm ρ K) (hinj : Function.Injective (prodHom hc))
    {B : Subgroup Y}
    (hB : (prodHom hc).range = B) (w : B) (l : Q → K) (hl : prodHom hc l = (w : Y)) :
    projHom hc hinj hB w = l 1 := by
  have h1 : (MonoidHom.ofInjective hinj).symm (Subgroup.inclusion hB.ge w) = l := by
    apply hinj
    rw [MonoidHom.apply_ofInjective_symm, Subgroup.coe_inclusion, hl]
  show ((MonoidHom.ofInjective hinj).symm (Subgroup.inclusion hB.ge w)) 1 = l 1
  rw [h1]

end Regular

section Cyclic

variable {Y : Type*} [Group Y]

private def zpHom (p : ℕ) [NeZero p] (a : Y) (ha : a ^ p = 1) :
    Multiplicative (ZMod p) →* Y where
  toFun q := a ^ (Multiplicative.toAdd q).val
  map_one' := by simp
  map_mul' x y := by
    simp only [toAdd_mul, ZMod.val_add]
    rw [← pow_eq_pow_mod _ ha, pow_add]

private theorem zpHom_apply (p : ℕ) [NeZero p] (a : Y) (ha : a ^ p = 1)
    (q : Multiplicative (ZMod p)) : zpHom p a ha q = a ^ (Multiplicative.toAdd q).val := rfl

private theorem zpHom_ofAdd_one (p : ℕ) [NeZero p] [Fact p.Prime] (a : Y) (ha : a ^ p = 1) :
    zpHom p a ha (Multiplicative.ofAdd 1) = a := by
  simp [zpHom_apply, ZMod.val_one]

private theorem exists_pow_eq (p : ℕ) [NeZero p] (y : Multiplicative (ZMod p)) :
    ∃ n : ℕ, y = (Multiplicative.ofAdd (1 : ZMod p)) ^ n := by
  refine ⟨(Multiplicative.toAdd y).val, ?_⟩
  have h : (Multiplicative.ofAdd (1 : ZMod p)) ^ (Multiplicative.toAdd y).val =
      Multiplicative.ofAdd (Multiplicative.toAdd y) := by
    rw [← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val]
  exact h.symm

private theorem iSup_range_conjEmb (p : ℕ) [NeZero p] (a : Y) (ha : a ^ p = 1) (K : Subgroup Y) :
    (⨆ x : Multiplicative (ZMod p), (conjEmb (zpHom p a ha) K x).range) = kstar p a K := by
  apply le_antisymm
  · refine iSup_le fun x => ?_
    refine le_trans ?_ (le_iSup (fun i : Fin p => kconj a K i)
      ⟨(Multiplicative.toAdd x).val, ZMod.val_lt _⟩)
    rintro _ ⟨k, rfl⟩
    exact Subgroup.mem_map.2 ⟨k, k.2, rfl⟩
  · refine iSup_le fun i => ?_
    refine le_trans ?_ (le_iSup (fun x => (conjEmb (zpHom p a ha) K x).range)
      (Multiplicative.ofAdd ((i : ℕ) : ZMod p)))
    rintro _ ⟨k, hk, rfl⟩
    refine ⟨⟨k, hk⟩, ?_⟩
    have hval : ((i : ℕ) : ZMod p).val = (i : ℕ) := ZMod.val_cast_of_lt i.2
    rw [conjEmb_apply, zpHom_apply]
    simp only [toAdd_ofAdd, hval]
    rfl

private theorem exists_mulSingle_of_mem_kconj (p : ℕ) [NeZero p] (a : Y) (ha : a ^ p = 1)
    {K : Subgroup Y} (hc : ConjComm (zpHom p a ha) K) (i : Fin p) {w : Y}
    (hw : w ∈ kconj a K i) :
    ∃ k : K, prodHom hc (Pi.mulSingle (Multiplicative.ofAdd ((i : ℕ) : ZMod p)) k) = w := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hw
  refine ⟨⟨k, hk⟩, ?_⟩
  rw [prodHom_mulSingle, zpHom_apply, toAdd_ofAdd, ZMod.val_cast_of_lt i.2]
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

private theorem mem_of_mem_kconj_zero {a : Y} {K : Subgroup Y} {y : Y} (hy : y ∈ kconj a K 0) :
    y ∈ K := by
  obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.1 hy
  simpa using hk

end Cyclic

theorem exists_diagonal {Y : Type*} [Group Y] [Finite Y] (p : ℕ) [hpp : Fact p.Prime]
    (K : Subgroup Y) (a : Y) (ha : a ^ p = 1)
    (hcomm : ∀ i j : Fin p, i ≠ j → ∀ x ∈ kconj a K i, ∀ y ∈ kconj a K j, x * y = y * x)
    (hcenter : ∀ z ∈ K, (∀ y ∈ K, z * y = y * z) → z = 1)
    (hcap : ∀ m : ℕ, 0 < m → m < p → a ^ m ∉ Subgroup.normalizer (K : Set Y)) :
    ∃ (Δ : ↥K →* Y) (π₀ : ↥(kstar p a K) →* ↥K),
      Function.Injective Δ ∧
      (∀ x : ↥K, Δ x ∈ kstar p a K ∧ Δ x * a = a * Δ x) ∧
      (∀ w ∈ kstar p a K, w * a = a * w → ∃ x : ↥K, Δ x = w) ∧
      (∀ (x y : ↥K), Δ x * (y : Y) * (Δ x)⁻¹ = (x : Y) * (y : Y) * (x : Y)⁻¹) ∧
      (∀ (x : ↥K) (h : Δ x ∈ kstar p a K), π₀ ⟨Δ x, h⟩ = x) ∧
      (∀ (k : ↥K) (h : (k : Y) ∈ kstar p a K), π₀ ⟨(k : Y), h⟩ = k) ∧
      (∀ (i : Fin p), i ≠ ⟨0, hpp.out.pos⟩ → ∀ w : ↥(kstar p a K), (w : Y) ∈ kconj a K i →
        π₀ w = 1) ∧
      (∀ s : Y, (∀ i : Fin p, s ∈ Subgroup.normalizer ((kconj a K i : Subgroup Y) : Set Y)) →
        ∀ (w : ↥(kstar p a K)) (h : s * (w : Y) * s⁻¹ ∈ kstar p a K),
          ((π₀ ⟨s * (w : Y) * s⁻¹, h⟩ : ↥K) : Y) = s * ((π₀ w : ↥K) : Y) * s⁻¹) := by
  haveI : NeZero p := ⟨hpp.out.ne_zero⟩
  have hc : ConjComm (zpHom p a ha) K := by
    intro x y hxy k l
    have hne : (⟨(Multiplicative.toAdd x).val, ZMod.val_lt _⟩ : Fin p) ≠
        ⟨(Multiplicative.toAdd y).val, ZMod.val_lt _⟩ := by
      intro h
      exact hxy (Multiplicative.toAdd.injective (ZMod.val_injective p (Fin.mk.inj h)))
    exact hcomm _ _ hne _ (Subgroup.mem_map.2 ⟨k, k.2, rfl⟩) _ (Subgroup.mem_map.2 ⟨l, l.2, rfl⟩)
  have hinj : Function.Injective (prodHom hc) := prodHom_injective hcenter hc
  have hB : (prodHom hc).range = kstar p a K :=
    (prodHom_range hc).trans (iSup_range_conjEmb p a ha K)
  obtain ⟨π₀, hπ⟩ : ∃ π₀ : ↥(kstar p a K) →* ↥K, ∀ (w : ↥(kstar p a K))
      (l : Multiplicative (ZMod p) → ↥K), prodHom hc l = (w : Y) → π₀ w = l 1 :=
    ⟨projHom hc hinj hB, fun w l hl => projHom_eq hc hinj hB w l hl⟩
  have h5 : ∀ (x : ↥K) (h : diagHom hc x ∈ kstar p a K), π₀ ⟨diagHom hc x, h⟩ = x :=
    fun x h => hπ ⟨_, h⟩ (fun _ => x) (diagHom_apply hc x).symm
  have h6 : ∀ (k : ↥K) (h : (k : Y) ∈ kstar p a K), π₀ ⟨(k : Y), h⟩ = k := by
    intro k h
    rw [hπ ⟨_, h⟩ (Pi.mulSingle 1 k) (prodHom_mulSingle_one hc k)]
    simp
  have h7 : ∀ (i : Fin p), i ≠ ⟨0, hpp.out.pos⟩ → ∀ w : ↥(kstar p a K), (w : Y) ∈ kconj a K i →
      π₀ w = 1 := by
    intro i hi w hw
    obtain ⟨k, hk⟩ := exists_mulSingle_of_mem_kconj p a ha hc i hw
    have hne : (1 : Multiplicative (ZMod p)) ≠ Multiplicative.ofAdd ((i : ℕ) : ZMod p) := by
      intro h
      apply hi
      have h0 : ((i : ℕ) : ZMod p) = 0 := (congrArg Multiplicative.toAdd h).symm
      have h1 := ZMod.val_cast_of_lt i.2
      rw [h0, ZMod.val_zero] at h1
      exact Fin.ext h1.symm
    rw [hπ w _ hk]
    exact Pi.mulSingle_eq_of_ne (M := fun _ : Multiplicative (ZMod p) => ↥K) hne k
  refine ⟨diagHom hc, π₀, diagHom_injective hcenter hc, ?_, ?_, diagHom_conj hc, h5, h6, h7, ?_⟩
  · intro x
    refine ⟨?_, ?_⟩
    · rw [← hB]
      exact ⟨fun _ => x, (diagHom_apply hc x).symm⟩
    · have h := diagHom_commute hc x (Multiplicative.ofAdd 1)
      rwa [zpHom_ofAdd_one] at h
  · intro w hw hwa
    rw [← hB] at hw
    obtain ⟨l, rfl⟩ := hw
    have hwa' : prodHom hc l * zpHom p a ha (Multiplicative.ofAdd 1) =
        zpHom p a ha (Multiplicative.ofAdd 1) * prodHom hc l := by
      rw [zpHom_ofAdd_one]
      exact hwa
    obtain ⟨x, hx⟩ := exists_const_of_commute hcenter hc (exists_pow_eq p) hwa'
    exact ⟨x, by rw [diagHom_apply, ← hx]⟩
  · intro s hs w hsw
    have key : ∀ y : Y, y ∈ kstar p a K → ∃ (hy : y ∈ kstar p a K)
        (hsy : s * y * s⁻¹ ∈ kstar p a K),
        ((π₀ ⟨s * y * s⁻¹, hsy⟩ : ↥K) : Y) = s * ((π₀ ⟨y, hy⟩ : ↥K) : Y) * s⁻¹ := by
      intro y hy
      have hy' : y ∈ ⨆ i : Fin p, kconj a K i := hy
      refine Subgroup.iSup_induction (fun i : Fin p => kconj a K i)
        (C := fun y => ∃ (hy : y ∈ kstar p a K) (hsy : s * y * s⁻¹ ∈ kstar p a K),
          ((π₀ ⟨s * y * s⁻¹, hsy⟩ : ↥K) : Y) = s * ((π₀ ⟨y, hy⟩ : ↥K) : Y) * s⁻¹)
        hy' ?_ ?_ ?_
      · intro i y hy
        have hyk : y ∈ kstar p a K := Subgroup.mem_iSup_of_mem i hy
        have hsy : s * y * s⁻¹ ∈ kconj a K i := (Subgroup.mem_normalizer_iff.1 (hs i) y).1 hy
        have hsyk : s * y * s⁻¹ ∈ kstar p a K := Subgroup.mem_iSup_of_mem i hsy
        refine ⟨hyk, hsyk, ?_⟩
        by_cases hi : i = ⟨0, hpp.out.pos⟩
        · subst hi
          have hyK : y ∈ K := mem_of_mem_kconj_zero hy
          have hsyK : s * y * s⁻¹ ∈ K := mem_of_mem_kconj_zero hsy
          have e1 : π₀ ⟨y, hyk⟩ = ⟨y, hyK⟩ := h6 ⟨y, hyK⟩ hyk
          have e2 : π₀ ⟨s * y * s⁻¹, hsyk⟩ = ⟨s * y * s⁻¹, hsyK⟩ := h6 ⟨s * y * s⁻¹, hsyK⟩ hsyk
          rw [e1, e2]
        · have e1 : π₀ ⟨y, hyk⟩ = 1 := h7 i hi ⟨y, hyk⟩ hy
          have e2 : π₀ ⟨s * y * s⁻¹, hsyk⟩ = 1 := h7 i hi ⟨s * y * s⁻¹, hsyk⟩ hsy
          rw [e1, e2]
          simp
      · have h1 : (1 : Y) ∈ kstar p a K := Subgroup.one_mem _
        have h2 : s * 1 * s⁻¹ ∈ kstar p a K := by simpa using h1
        refine ⟨h1, h2, ?_⟩
        have e1 : (⟨1, h1⟩ : ↥(kstar p a K)) = 1 := rfl
        have e2 : (⟨s * 1 * s⁻¹, h2⟩ : ↥(kstar p a K)) = 1 := Subtype.ext (by simp)
        rw [e1, e2, map_one]
        simp
      · rintro y₁ y₂ ⟨hy₁, hs₁, e₁⟩ ⟨hy₂, hs₂, e₂⟩
        have hy : y₁ * y₂ ∈ kstar p a K := Subgroup.mul_mem _ hy₁ hy₂
        have hsplit : s * (y₁ * y₂) * s⁻¹ = (s * y₁ * s⁻¹) * (s * y₂ * s⁻¹) := by group
        have hs' : s * (y₁ * y₂) * s⁻¹ ∈ kstar p a K := by
          rw [hsplit]
          exact Subgroup.mul_mem _ hs₁ hs₂
        refine ⟨hy, hs', ?_⟩
        have e3 : (⟨s * (y₁ * y₂) * s⁻¹, hs'⟩ : ↥(kstar p a K)) =
            ⟨s * y₁ * s⁻¹, hs₁⟩ * ⟨s * y₂ * s⁻¹, hs₂⟩ := Subtype.ext hsplit
        have e4 : (⟨y₁ * y₂, hy⟩ : ↥(kstar p a K)) = ⟨y₁, hy₁⟩ * ⟨y₂, hy₂⟩ := rfl
        rw [e3, e4, map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul, e₁, e₂]
        group
    obtain ⟨hw', hsw', e⟩ := key (w : Y) w.2
    exact e

end CFSG.LocalAnalysis.GLTheoremB.MovingAround.Lemma129W3

end
