module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.SquareGeneric
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabThreeSpin
import CFSG.LocalAnalysis.AGLEmbeddingD2.CyclicSylowGL
public import CFSG.Assembly.Subnormal
public import CFSG.LieType.Steinberg.Classical.SpinFrame
public import CFSG.LieType.Steinberg.Exceptional.E6E7
public import CFSG.LieType.Steinberg.Families
public import CFSG.LieType.Steinberg.G2
public import CFSG.LieType.Universal.Spin.Generation
public import CFSG.LieType.Universal.Spin.OddCT
public import CFSG.LieType.Universal.Spin.PlusCT
public import CFSG.LieType.Universal.Spin.Structure
public import CFSG.LieType.Universal.SpinOmega
public import CFSG.LieType.Universal.Unitary
public import TauCeti.LinearAlgebra.CliffordAlgebra.Monomials

public section

namespace CFSG.AGLEmbeddingD2.SquareSpinPlus

open CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbedding.ParabPrime CFSG.AGLEmbeddingD2.ParabLevi
  CFSG.AGLEmbeddingD2.ParabRankEngine CFSG.AGLEmbeddingD2.SquareGeneric QuadraticMap

section Coordinates

variable {n : ℕ} {F : Type} [Field F]

@[expose] def frameCoord (m : Fin n) (r : Bool) : Fin n ⊕ Fin n := if r then .inl m else .inr m

@[expose] def coordIdx (z : Fin n ⊕ Fin n) : Fin n := z.elim id id

@[simp] theorem frameCoord_true (m : Fin n) : frameCoord m true = .inl m := rfl

@[simp] theorem frameCoord_false (m : Fin n) : frameCoord m false = .inr m := rfl

@[simp] theorem coordIdx_inl (m : Fin n) : coordIdx (.inl m : Fin n ⊕ Fin n) = m := rfl

@[simp] theorem coordIdx_inr (m : Fin n) : coordIdx (.inr m : Fin n ⊕ Fin n) = m := rfl

@[simp] theorem coordIdx_frameCoord (m : Fin n) (r : Bool) : coordIdx (frameCoord m r) = m := by
  cases r <;> rfl

@[simp] theorem coordIdx_swap (z : Fin n ⊕ Fin n) : coordIdx z.swap = coordIdx z := by
  cases z <;> rfl

theorem swap_frameCoord (m : Fin n) (r : Bool) :
    (frameCoord m r).swap = frameCoord m (!r) := by
  cases r <;> rfl

theorem frameCoord_eq_frameCoord_iff {m m' : Fin n} {r r' : Bool} :
    frameCoord m r = frameCoord m' r' ↔ m = m' ∧ r = r' := by
  cases r <;> cases r' <;> simp [frameCoord]

theorem plusVec_eq_single (m : Fin n) (r : Bool) :
    plusVec n F m r = Pi.single (frameCoord m r) 1 := by
  cases r <;> rfl

theorem polar_quadPlus_single_swap (v : Fin n ⊕ Fin n → F) (z : Fin n ⊕ Fin n) :
    polar (quadPlus n F) v (Pi.single z 1) = v z.swap := by
  cases z
  · exact polar_quadPlus_single_inl n F v _
  · exact polar_quadPlus_single_inr n F v _

theorem spinAction_longRoot_apply (hn : 3 ≤ n) {i j : Fin n} (hij : i ≠ j) (s t : Bool) (c : F)
    (v : Fin n ⊕ Fin n → F) :
    spinAction (quadPlus n F) ((plusFrame n F hn).longRoot hij s t (.ofAdd c)) v =
      v + (c * v (frameCoord j t).swap) • Pi.single (frameCoord i s) 1 -
        (c * v (frameCoord i s).swap) • Pi.single (frameCoord j t) 1 := by
  rw [HypFrame.spinAction_longRoot, plusFrame_vec, plusVec_eq_single, plusVec_eq_single,
    polar_quadPlus_single_swap, polar_quadPlus_single_swap]

end Coordinates

section Restriction

variable {n : ℕ} {F : Type} [Field F]

@[expose] def cspan (T : Set (Fin n ⊕ Fin n)) : Submodule F (Fin n ⊕ Fin n → F) :=
  Submodule.span F ((fun z => (Pi.single z 1 : Fin n ⊕ Fin n → F)) '' T)

theorem single_mem_cspan {T : Set (Fin n ⊕ Fin n)} {z : Fin n ⊕ Fin n} (hz : z ∈ T) :
    (Pi.single z 1 : Fin n ⊕ Fin n → F) ∈ cspan T :=
  Submodule.subset_span ⟨z, hz, rfl⟩

theorem apply_eq_zero_of_mem_cspan {T : Set (Fin n ⊕ Fin n)} {v : Fin n ⊕ Fin n → F}
    (hv : v ∈ cspan T) {z : Fin n ⊕ Fin n} (hz : z ∉ T) : v z = 0 := by
  induction hv using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨y, hy, rfl⟩ := hx
    have hzy : z ≠ y := fun h => hz (h ▸ hy)
    exact Pi.single_eq_of_ne hzy _
  | zero => rfl
  | add x y _ _ hx hy => simp [hx, hy]
  | smul a x _ hx => simp [hx]

@[expose] def stab (T : Set (Fin n ⊕ Fin n)) : Subgroup (spinGroup (quadPlus n F)) where
  carrier := {g | (∀ v ∈ cspan (F := F) T, spinAction (quadPlus n F) g v ∈ cspan T) ∧
    ∀ v ∈ cspan (F := F) T, spinAction (quadPlus n F) g⁻¹ v ∈ cspan T}
  mul_mem' := by
    rintro g h ⟨hg, hg'⟩ ⟨hh, hh'⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_mul, LinearEquiv.mul_apply]
      exact hg _ (hh v hv)
    · rw [mul_inv_rev, map_mul, LinearEquiv.mul_apply]
      exact hh' _ (hg' v hv)
  one_mem' := ⟨fun v hv => by rwa [map_one], fun v hv => by rwa [inv_one, map_one]⟩
  inv_mem' := by
    rintro g ⟨hg, hg'⟩
    exact ⟨fun v hv => by simpa using hg' v hv, fun v hv => by simpa using hg v hv⟩

@[expose] def fixing (R : Set (Fin n ⊕ Fin n)) : Subgroup (spinGroup (quadPlus n F)) where
  carrier := {g | ∀ z ∈ R, spinAction (quadPlus n F) g (Pi.single z 1) = Pi.single z 1}
  mul_mem' := by
    intro g h hg hh z hz
    rw [map_mul, LinearEquiv.mul_apply, hh z hz, hg z hz]
  one_mem' := fun z _ => by rw [map_one]; rfl
  inv_mem' := by
    intro g hg z hz
    conv_lhs => rw [← hg z hz]
    rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
    rfl

theorem map_cspan_eq {T : Set (Fin n ⊕ Fin n)} {g : spinGroup (quadPlus n F)}
    (hg : g ∈ stab (F := F) T) :
    (cspan (F := F) T).map (spinAction (quadPlus n F) g : (Fin n ⊕ Fin n → F) →ₗ[F] _) =
      cspan T := by
  apply le_antisymm
  · rintro _ ⟨v, hv, rfl⟩
    exact hg.1 v hv
  · intro v hv
    refine ⟨spinAction (quadPlus n F) g⁻¹ v, hg.2 v hv, ?_⟩
    change spinAction (quadPlus n F) g (spinAction (quadPlus n F) g⁻¹ v) = v
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
    rfl

@[expose] noncomputable def resHom (T : Set (Fin n ⊕ Fin n)) :
    ↥(stab (F := F) T) →* (cspan (F := F) T ≃ₗ[F] cspan (F := F) T) where
  toFun g := (spinAction (quadPlus n F) g).ofSubmodules (cspan T) (cspan T) (map_cspan_eq g.2)
  map_one' := LinearEquiv.ext fun v => Subtype.ext (by simp)
  map_mul' g h := LinearEquiv.ext fun v => Subtype.ext (by simp)

theorem spinAction_injective [CharP F 2] : Function.Injective (spinAction (quadPlus n F)) := by
  rw [← MonoidHom.ker_eq_bot_iff, ← ker_spinMatrix]
  exact ker_spinMatrix_quadPlus_eq_bot CharTwo.two_eq_zero

theorem spinAction_eq_one_of_forall_single {g : spinGroup (quadPlus n F)}
    (h : ∀ z, spinAction (quadPlus n F) g (Pi.single z 1) = Pi.single z 1) :
    spinAction (quadPlus n F) g = 1 := by
  have h1 : ((spinAction (quadPlus n F) g : (Fin n ⊕ Fin n → F) ≃ₗ[F] _) :
      (Fin n ⊕ Fin n → F) →ₗ[F] _) = LinearMap.id :=
    (Pi.basisFun F (Fin n ⊕ Fin n)).ext fun z => by simpa [Pi.basisFun_apply] using h z
  exact LinearEquiv.ext (LinearMap.congr_fun h1)

theorem exists_injective_restrict [CharP F 2] {G : Subgroup (spinGroup (quadPlus n F))}
    {T₁ T₂ R : Set (Fin n ⊕ Fin n)} (hG₁ : G ≤ stab T₁) (hG₂ : G ≤ stab T₂)
    (hG₃ : G ≤ fixing R) (hdual : ∀ z ∈ T₂, z.swap ∈ T₁)
    (hcover : ∀ z, z ∉ R → z ∈ T₁ ∨ z ∈ T₂) :
    ∃ φ : ↥G →* (cspan (F := F) T₁ ≃ₗ[F] cspan (F := F) T₁), Function.Injective φ := by
  refine ⟨(resHom T₁).comp (Subgroup.inclusion hG₁), ?_⟩
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  rintro ⟨g, hg⟩ hker
  have h1 : ∀ z ∈ T₁, spinAction (quadPlus n F) g (Pi.single z 1) = Pi.single z 1 := fun z hz => by
    have := congrArg Subtype.val (LinearEquiv.congr_fun (MonoidHom.mem_ker.mp hker)
      ⟨Pi.single z 1, single_mem_cspan hz⟩)
    exact this
  have h2 : ∀ z ∈ T₂, spinAction (quadPlus n F) g (Pi.single z 1) = Pi.single z 1 := by
    intro z hz
    set w := spinAction (quadPlus n F) g (Pi.single z 1) - Pi.single z 1 with hw
    have hw0 : w = 0 := by
      funext y
      by_cases hy : y ∈ T₂
      · have hys : y.swap ∈ T₁ := hdual y hy
        have hpol : polar (quadPlus n F) w (Pi.single y.swap 1) = w y := by
          rw [polar_quadPlus_single_swap, Sum.swap_swap]
        rw [← hpol, hw, polar_sub_left]
        have := polar_spinAction (quadPlus n F) g (Pi.single z 1) (Pi.single y.swap 1)
        rw [h1 _ hys] at this
        rw [this, sub_self]
        rfl
      · have hzy : y ≠ z := fun h => hy (h ▸ hz)
        have := apply_eq_zero_of_mem_cspan ((hG₂ hg).1 _ (single_mem_cspan hz)) hy
        simp [hw, this, hzy]
    exact sub_eq_zero.mp hw0
  have h3 : ∀ z, spinAction (quadPlus n F) g (Pi.single z 1) = Pi.single z 1 := by
    intro z
    by_cases hz : z ∈ R
    · exact hG₃ hg z hz
    · rcases hcover z hz with h | h
      · exact h1 z h
      · exact h2 z h
  have hone : spinAction (quadPlus n F) g = 1 := spinAction_eq_one_of_forall_single h3
  have : g = 1 := spinAction_injective (by rw [hone, map_one])
  exact Subtype.ext this

end Restriction

section FiveRank

variable {n : ℕ} {F : Type} [Field F]

theorem finrank_cspan_le (T : Finset (Fin n ⊕ Fin n)) :
    Module.finrank F (cspan (F := F) (T : Set (Fin n ⊕ Fin n))) ≤ T.card := by
  classical
  have h : cspan (F := F) (T : Set (Fin n ⊕ Fin n)) = Submodule.span F
      (↑(T.image fun z => (Pi.single z 1 : Fin n ⊕ Fin n → F)) : Set (Fin n ⊕ Fin n → F)) := by
    rw [cspan, Finset.coe_image]
  rw [h]
  exact (finrank_span_finset_le_card _).trans Finset.card_image_le

theorem isCyclic_of_isPGroup_five_of_stab [Finite F] [CharP F 2] {f : ℕ} (hf : Odd f)
    (hFf : Nat.card F = 2 ^ f) {G : Subgroup (spinGroup (quadPlus n F))}
    {T₁ : Finset (Fin n ⊕ Fin n)} {T₂ R : Set (Fin n ⊕ Fin n)} (hT₁ : T₁.card ≤ 7)
    (hG₁ : G ≤ stab (T₁ : Set (Fin n ⊕ Fin n))) (hG₂ : G ≤ stab T₂) (hG₃ : G ≤ fixing R)
    (hdual : ∀ z ∈ T₂, z.swap ∈ (T₁ : Set (Fin n ⊕ Fin n)))
    (hcover : ∀ z, z ∉ R → z ∈ (T₁ : Set (Fin n ⊕ Fin n)) ∨ z ∈ T₂)
    (P : Subgroup (spinGroup (quadPlus n F))) (hPG : P ≤ G) (hP : IsPGroup 5 P) : IsCyclic P := by
  classical
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨φ, hφ⟩ := exists_injective_restrict hG₁ hG₂ hG₃ hdual hcover
  let ψ : ↥G →* LinearMap.GeneralLinearGroup F (cspan (F := F) (T₁ : Set (Fin n ⊕ Fin n))) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F _).symm.toMonoidHom.comp φ
  have hψ : Function.Injective ψ := fun a b h =>
    hφ ((LinearMap.GeneralLinearGroup.generalLinearEquiv F _).symm.injective h)
  have hc := CyclicSylowGL.isCyclic_of_isPGroup_five_of_injective_GeneralLinearGroup_two_pow hf
    (by rw [← Nat.card_eq_fintype_card, hFf]) ((finrank_cspan_le T₁).trans hT₁) ψ hψ
    (P.subgroupOf G) (hP.comap_of_injective _ (Subgroup.subtype_injective _))
  exact (Subgroup.subgroupOfEquivOfLe hPG).isCyclic.mp hc

end FiveRank

section Nodes

variable {n : ℕ} {F : Type} [Field F]

@[expose] def nodeX (k : Fin n) : Fin n ⊕ Fin n := frameCoord (rootIdxD n k) true

@[expose] def nodeY (k : Fin n) : Fin n ⊕ Fin n := frameCoord (rootIdxD' n k) (rootSignD n k)

@[simp] theorem coordIdx_nodeX (k : Fin n) : coordIdx (nodeX k) = rootIdxD n k :=
  coordIdx_frameCoord _ _

@[simp] theorem coordIdx_nodeY (k : Fin n) : coordIdx (nodeY k) = rootIdxD' n k :=
  coordIdx_frameCoord _ _

@[expose] def Balanced (T : Set (Fin n ⊕ Fin n)) (k : Fin n) : Prop :=
  ((nodeY k).swap ∈ T ↔ nodeX k ∈ T) ∧ ((nodeX k).swap ∈ T ↔ nodeY k ∈ T)

theorem Balanced.swap {T : Set (Fin n ⊕ Fin n)} {k : Fin n} (h : Balanced T k) :
    Balanced (Sum.swap '' T) k := by
  obtain ⟨h1, h2⟩ := h
  have hm : ∀ z : Fin n ⊕ Fin n, z.swap ∈ Sum.swap '' T ↔ z ∈ T := fun z =>
    Sum.swap_leftInverse.injective.mem_set_image
  have hm' : ∀ z : Fin n ⊕ Fin n, z ∈ Sum.swap '' T ↔ z.swap ∈ T := fun z => by
    rw [← hm, Sum.swap_swap]
  rw [Balanced, hm, hm', hm, hm']
  exact ⟨h2.symm, h1.symm⟩

theorem transvect_mem_cspan {T : Set (Fin n ⊕ Fin n)} {x y : Fin n ⊕ Fin n} (c : F)
    (h1 : y.swap ∈ T → x ∈ T) (h2 : x.swap ∈ T → y ∈ T) {v : Fin n ⊕ Fin n → F}
    (hv : v ∈ cspan T) :
    v + (c * v y.swap) • (Pi.single x 1 : Fin n ⊕ Fin n → F) -
      (c * v x.swap) • (Pi.single y 1 : Fin n ⊕ Fin n → F) ∈ cspan T := by
  refine sub_mem (add_mem hv ?_) ?_
  · by_cases hy : y.swap ∈ T
    · exact Submodule.smul_mem _ _ (single_mem_cspan (h1 hy))
    · rw [apply_eq_zero_of_mem_cspan hv hy, mul_zero, zero_smul]
      exact zero_mem _
  · by_cases hx : x.swap ∈ T
    · exact Submodule.smul_mem _ _ (single_mem_cspan (h2 hx))
    · rw [apply_eq_zero_of_mem_cspan hv hx, mul_zero, zero_smul]
      exact zero_mem _

theorem spinAction_rootD (hn : 3 ≤ n) (k : Fin n) (c : F) (v : Fin n ⊕ Fin n → F) :
    spinAction (quadPlus n F) (rootD F hn k (.ofAdd c)) v =
      v + (c * v (nodeY k).swap) • (Pi.single (nodeX k) 1 : Fin n ⊕ Fin n → F) -
        (c * v (nodeX k).swap) • (Pi.single (nodeY k) 1 : Fin n ⊕ Fin n → F) :=
  spinAction_longRoot_apply hn (rootIdxD_ne n (by omega) k) true (rootSignD n k) c v

theorem spinAction_negRootD (hn : 3 ≤ n) (k : Fin n) (c : F) (v : Fin n ⊕ Fin n → F) :
    spinAction (quadPlus n F) (negRootD F hn k (.ofAdd c)) v =
      v + (c * v (nodeX k)) • (Pi.single (nodeY k).swap 1 : Fin n ⊕ Fin n → F) -
        (c * v (nodeY k)) • (Pi.single (nodeX k).swap 1 : Fin n ⊕ Fin n → F) := by
  rw [negRootD, spinAction_longRoot_apply hn (rootIdxD_ne n (by omega) k).symm (!rootSignD n k)
    false c v]
  simp [nodeX, nodeY, swap_frameCoord]

theorem rootD_mem_stab (hn : 3 ≤ n) {T : Set (Fin n ⊕ Fin n)} {k : Fin n} (hT : Balanced T k)
    (c : Multiplicative F) : rootD F hn k c ∈ stab (F := F) T := by
  have key : ∀ c' : Multiplicative F, ∀ v ∈ cspan (F := F) T,
      spinAction (quadPlus n F) (rootD F hn k c') v ∈ cspan T := by
    intro c' v hv
    rw [← ofAdd_toAdd c', spinAction_rootD]
    exact transvect_mem_cspan _ hT.1.mp hT.2.mp hv
  exact ⟨key c, fun v hv => by rw [← map_inv]; exact key _ v hv⟩

theorem negRootD_mem_stab (hn : 3 ≤ n) {T : Set (Fin n ⊕ Fin n)} {k : Fin n} (hT : Balanced T k)
    (c : Multiplicative F) : negRootD F hn k c ∈ stab (F := F) T := by
  have key : ∀ c' : Multiplicative F, ∀ v ∈ cspan (F := F) T,
      spinAction (quadPlus n F) (negRootD F hn k c') v ∈ cspan T := by
    intro c' v hv
    rw [← ofAdd_toAdd c', spinAction_negRootD]
    have := transvect_mem_cspan (x := (nodeY k).swap) (y := (nodeX k).swap)
      (Multiplicative.toAdd c') (by simpa using hT.1.mpr) (by simpa using hT.2.mpr) hv
    simpa using this
  exact ⟨key c, fun v hv => by rw [← map_inv]; exact key _ v hv⟩

theorem rootD_mem_fixing (hn : 3 ≤ n) {R : Set (Fin n ⊕ Fin n)} {k : Fin n}
    (hR : ∀ z ∈ R, coordIdx z ≠ rootIdxD n k ∧ coordIdx z ≠ rootIdxD' n k)
    (c : Multiplicative F) : rootD F hn k c ∈ fixing (F := F) R := by
  intro z hz
  rw [← ofAdd_toAdd c, spinAction_rootD]
  have h1 : (Pi.single z 1 : Fin n ⊕ Fin n → F) (nodeY k).swap = 0 :=
    Pi.single_eq_of_ne (fun h => (hR z hz).2 (by rw [← h, coordIdx_swap, coordIdx_nodeY])) _
  have h2 : (Pi.single z 1 : Fin n ⊕ Fin n → F) (nodeX k).swap = 0 :=
    Pi.single_eq_of_ne (fun h => (hR z hz).1 (by rw [← h, coordIdx_swap, coordIdx_nodeX])) _
  simp [h1, h2]

theorem negRootD_mem_fixing (hn : 3 ≤ n) {R : Set (Fin n ⊕ Fin n)} {k : Fin n}
    (hR : ∀ z ∈ R, coordIdx z ≠ rootIdxD n k ∧ coordIdx z ≠ rootIdxD' n k)
    (c : Multiplicative F) : negRootD F hn k c ∈ fixing (F := F) R := by
  intro z hz
  rw [← ofAdd_toAdd c, spinAction_negRootD]
  have h1 : (Pi.single z 1 : Fin n ⊕ Fin n → F) (nodeX k) = 0 :=
    Pi.single_eq_of_ne (fun h => (hR z hz).1 (by rw [← h, coordIdx_nodeX])) _
  have h2 : (Pi.single z 1 : Fin n ⊕ Fin n → F) (nodeY k) = 0 :=
    Pi.single_eq_of_ne (fun h => (hR z hz).2 (by rw [← h, coordIdx_nodeY])) _
  simp [h1, h2]

theorem leviM_le_stab (hn : 3 ≤ n) {I : Set (Fin n)} {T : Set (Fin n ⊕ Fin n)}
    (hT : ∀ k ∈ I, Balanced T k) : leviM (plusDatum n F hn) I ≤ stab (F := F) T := by
  refine iSup₂_le fun (k : Fin n) hk => sup_le ?_ ?_
  · change plusRootGroup n F hn (Pi.single k 1) ≤ _
    rw [plusRootGroup_single]
    rintro _ ⟨c, rfl⟩
    exact rootD_mem_stab hn (hT k hk) c
  · change plusRootGroup n F hn (-Pi.single k 1) ≤ _
    rw [plusRootGroup_neg_single]
    rintro _ ⟨c, rfl⟩
    exact negRootD_mem_stab hn (hT k hk) c

theorem leviM_le_fixing (hn : 3 ≤ n) {I : Set (Fin n)} {S : Finset (Fin n)}
    (hS : ∀ k ∈ I, rootIdxD n k ∈ S ∧ rootIdxD' n k ∈ S) :
    leviM (plusDatum n F hn) I ≤ fixing (F := F) {z | coordIdx z ∉ S} := by
  refine iSup₂_le fun (k : Fin n) hk => sup_le ?_ ?_
  · change plusRootGroup n F hn (Pi.single k 1) ≤ _
    rw [plusRootGroup_single]
    rintro _ ⟨c, rfl⟩
    exact rootD_mem_fixing hn (R := {z | coordIdx z ∉ S}) (fun z (hz : coordIdx z ∉ S) =>
      ⟨fun h => hz (h ▸ (hS k hk).1), fun h => hz (h ▸ (hS k hk).2)⟩) c
  · change plusRootGroup n F hn (-Pi.single k 1) ≤ _
    rw [plusRootGroup_neg_single]
    rintro _ ⟨c, rfl⟩
    exact negRootD_mem_fixing hn (R := {z | coordIdx z ∉ S}) (fun z (hz : coordIdx z ∉ S) =>
      ⟨fun h => hz (h ▸ (hS k hk).1), fun h => hz (h ▸ (hS k hk).2)⟩) c

theorem isCyclic_of_isPGroup_five_leviM [Finite F] [CharP F 2] {f : ℕ} (hf : Odd f)
    (hFf : Nat.card F = 2 ^ f) (hn : 3 ≤ n) {I : Set (Fin n)} {S : Finset (Fin n)}
    {T₁ : Finset (Fin n ⊕ Fin n)} {T₂ : Set (Fin n ⊕ Fin n)}
    (hS : ∀ k ∈ I, rootIdxD n k ∈ S ∧ rootIdxD' n k ∈ S)
    (hB₁ : ∀ k ∈ I, Balanced (T₁ : Set (Fin n ⊕ Fin n)) k) (hB₂ : ∀ k ∈ I, Balanced T₂ k)
    (hdual : ∀ z ∈ T₂, z.swap ∈ (T₁ : Set (Fin n ⊕ Fin n)))
    (hcover : ∀ z, coordIdx z ∈ S → z ∈ (T₁ : Set (Fin n ⊕ Fin n)) ∨ z ∈ T₂)
    (hT₁ : T₁.card ≤ 7) (P : Subgroup (spinGroup (quadPlus n F)))
    (hP : P ≤ leviM (plusDatum n F hn) I) (h5 : IsPGroup 5 P) : IsCyclic P :=
  isCyclic_of_isPGroup_five_of_stab hf hFf (R := {z | coordIdx z ∉ S}) hT₁ (leviM_le_stab hn hB₁)
    (leviM_le_stab hn hB₂) (leviM_le_fixing hn hS) hdual
    (fun z hz => hcover z (not_not.mp hz)) P hP h5

end Nodes

section Support

theorem exists_finset_card_le_six {ι : Type*} (c : ι → ℕ) (I : Set ι)
    (hI : ¬ ∃ a ∈ I, ∃ b ∈ I, ∃ d ∈ I, c a + 2 ≤ c b ∧ c b + 2 ≤ c d) :
    ∃ t : Finset ℕ, t.card ≤ 6 ∧ ∀ k ∈ I, c k ∈ t ∧ c k + 1 ∈ t := by
  by_cases hne : I.Nonempty
  · obtain ⟨a, ha, hamin⟩ : ∃ a ∈ I, ∀ x ∈ I, c a ≤ c x := by
      obtain ⟨a, ha, hmin⟩ := (InvImage.wf c wellFounded_lt).has_min I hne
      exact ⟨a, ha, fun x hx => not_lt.1 (hmin x hx)⟩
    by_cases hne2 : ∃ x ∈ I, c a + 2 ≤ c x
    · obtain ⟨b, ⟨hb, hab2⟩, hbmin⟩ := (InvImage.wf c wellFounded_lt).has_min
        {x | x ∈ I ∧ c a + 2 ≤ c x} (by obtain ⟨x, hx, hax⟩ := hne2; exact ⟨x, hx, hax⟩)
      refine ⟨{c a, c a + 1, c a + 2, c b, c b + 1, c b + 2}, Finset.card_le_six, fun x hx => ?_⟩
      have hamin' := hamin x hx
      by_cases hx2 : c a + 2 ≤ c x
      · have hbx : c b ≤ c x := not_lt.1 (hbmin x ⟨hx, hx2⟩)
        have hxb : c x ≤ c b + 1 := by
          by_contra hc
          exact hI ⟨a, ha, b, hb, x, hx, hab2, by omega⟩
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      · simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
    · push Not at hne2
      refine ⟨{c a, c a + 1, c a + 2}, Finset.card_le_three.trans (by norm_num), fun x hx => ?_⟩
      have hamin' := hamin x hx
      have := hne2 x hx
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
  · rw [Set.not_nonempty_iff_eq_empty] at hne
    exact ⟨∅, by simp, fun k hk => by simp [hne] at hk⟩

variable {n : ℕ}

theorem val_rootIdxD (k : Fin n) :
    (rootIdxD n k).val = if k.val + 1 < n then k.val else n - 2 := by
  unfold rootIdxD
  split_ifs <;> rfl

theorem cartanD_eq_zero_of_not_adj {a b : Fin n} (hab : a ≠ b)
    (h : ¬ ((a.val + 1 = b.val ∧ b.val + 1 < n) ∨ (b.val + 1 = a.val ∧ a.val + 1 < n) ∨
      (a.val + 3 = n ∧ b.val + 1 = n) ∨ (b.val + 3 = n ∧ a.val + 1 = n))) :
    cartanD n a b = 0 := by
  simp only [cartanD, Matrix.of_apply, hab, ite_false]
  rw [ite_eq_right_iff]
  exact fun hadj => absurd hadj h

theorem cartanD_eq_zero_of_far {a b : Fin n}
    (h : (rootIdxD n a).val + 2 ≤ (rootIdxD n b).val) : a ≠ b ∧ cartanD n a b = 0 := by
  have hab : a ≠ b := by
    rintro rfl
    omega
  refine ⟨hab, cartanD_eq_zero_of_not_adj hab ?_⟩
  simp only [val_rootIdxD] at h
  split_ifs at h <;> omega

theorem exists_support (I : Set (Fin n))
    (hI : ¬ ∃ a ∈ I, ∃ b ∈ I, ∃ d ∈ I, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ cartanD n a b = 0 ∧
      cartanD n a d = 0 ∧ cartanD n b d = 0) :
    ∃ t : Finset ℕ, t.card ≤ 6 ∧
      ∀ k ∈ I, (rootIdxD n k).val ∈ t ∧ (rootIdxD n k).val + 1 ∈ t := by
  refine exists_finset_card_le_six (fun k => (rootIdxD n k).val) I ?_
  rintro ⟨a, ha, b, hb, d, hd, hab, hbd⟩
  obtain ⟨h1, h2⟩ := cartanD_eq_zero_of_far hab
  obtain ⟨h3, h4⟩ := cartanD_eq_zero_of_far hbd
  obtain ⟨h5, h6⟩ := cartanD_eq_zero_of_far (a := a) (b := d) (by omega)
  exact hI ⟨a, ha, b, hb, d, hd, h1, h5, h3, h2, h6, h4⟩

theorem le_add_three_of_ends (I : Set (Fin n))
    (hI : ¬ ∃ a ∈ I, ∃ b ∈ I, ∃ d ∈ I, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ cartanD n a b = 0 ∧
      cartanD n a d = 0 ∧ cartanD n b d = 0) {a b : Fin n} (ha : a ∈ I) (hb : b ∈ I)
    (ha' : a.val + 2 = n) (hb' : b.val + 1 = n) {k : Fin n} (hk : k ∈ I) : n ≤ k.val + 3 := by
  by_contra hlt
  push Not at hlt
  have hka : k ≠ a := fun h => by rw [h] at hlt; omega
  have hkb : k ≠ b := fun h => by rw [h] at hlt; omega
  have hab : a ≠ b := fun h => by rw [h] at ha'; omega
  exact hI ⟨k, hk, a, ha, b, hb, hka, hkb, hab, cartanD_eq_zero_of_not_adj hka (by omega),
    cartanD_eq_zero_of_not_adj hkb (by omega), cartanD_eq_zero_of_not_adj hab (by omega)⟩

end Support

section Signs

variable {n : ℕ}

@[expose] def signSet (S : Finset (Fin n)) (sg : Fin n → Bool) : Finset (Fin n ⊕ Fin n) :=
  S.image fun m => frameCoord m (sg m)

theorem frameCoord_mem_signSet {S : Finset (Fin n)} {sg : Fin n → Bool} {m : Fin n} {r : Bool} :
    frameCoord m r ∈ signSet S sg ↔ m ∈ S ∧ r = sg m := by
  simp only [signSet, Finset.mem_image, frameCoord_eq_frameCoord_iff]
  constructor
  · rintro ⟨m', hm', rfl, h⟩
    exact ⟨hm', h.symm⟩
  · rintro ⟨hm, rfl⟩
    exact ⟨m, hm, rfl, rfl⟩

theorem card_signSet_le (S : Finset (Fin n)) (sg : Fin n → Bool) :
    (signSet S sg).card ≤ S.card := Finset.card_image_le

theorem balanced_signSet {S : Finset (Fin n)} {sg : Fin n → Bool} {k : Fin n}
    (hx : rootIdxD n k ∈ S) (hy : rootIdxD' n k ∈ S)
    (h : sg (rootIdxD n k) = true ↔ sg (rootIdxD' n k) = !rootSignD n k) :
    Balanced (signSet S sg : Set (Fin n ⊕ Fin n)) k := by
  simp only [Balanced, nodeX, nodeY, swap_frameCoord, Finset.mem_coe, frameCoord_mem_signSet, hx,
    hy, true_and]
  revert h
  generalize sg (rootIdxD n k) = a
  generalize sg (rootIdxD' n k) = b
  generalize rootSignD n k = t
  cases a <;> cases b <;> cases t <;> simp

theorem mem_signSet_or_swap {S : Finset (Fin n)} (sg : Fin n → Bool) {z : Fin n ⊕ Fin n}
    (hz : coordIdx z ∈ S) :
    z ∈ (signSet S sg : Set (Fin n ⊕ Fin n)) ∨
      z ∈ Sum.swap '' (signSet S sg : Set (Fin n ⊕ Fin n)) := by
  have hz' : z = frameCoord (coordIdx z) (z.isLeft) := by cases z <;> rfl
  by_cases hsg : z.isLeft = sg (coordIdx z)
  · left
    rw [Finset.mem_coe, hz', frameCoord_mem_signSet]
    exact ⟨hz, hsg⟩
  · right
    refine ⟨z.swap, ?_, Sum.swap_swap z⟩
    rw [Finset.mem_coe, hz', swap_frameCoord, frameCoord_mem_signSet]
    refine ⟨hz, ?_⟩
    clear hz'
    revert hsg
    generalize z.isLeft = a
    generalize sg (coordIdx z) = b
    cases a <;> cases b <;> simp

theorem mem_disjSum_iff {S : Finset (Fin n)} {z : Fin n ⊕ Fin n} :
    z ∈ S.disjSum S ↔ coordIdx z ∈ S := by
  cases z <;> simp [coordIdx]

theorem balanced_disjSum {S : Finset (Fin n)} {k : Fin n} (hx : rootIdxD n k ∈ S)
    (hy : rootIdxD' n k ∈ S) : Balanced (↑(S.disjSum S) : Set (Fin n ⊕ Fin n)) k := by
  simp [Balanced, mem_disjSum_iff, hx, hy]

theorem balanced_empty (k : Fin n) : Balanced (∅ : Set (Fin n ⊕ Fin n)) k := by
  simp [Balanced]

@[expose] def supportOf (t : Finset ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun m => m.val ∈ t

theorem mem_supportOf {t : Finset ℕ} {m : Fin n} : m ∈ supportOf t ↔ m.val ∈ t := by
  simp [supportOf]

theorem card_supportOf_le (t : Finset ℕ) : (supportOf (n := n) t).card ≤ t.card :=
  Finset.card_le_card_of_injOn Fin.val (fun _ hm => mem_supportOf.1 hm) Fin.val_injective.injOn

theorem rootIdx_mem_supportOf (hn : 2 ≤ n) {I : Set (Fin n)} {t : Finset ℕ}
    (ht : ∀ k ∈ I, (rootIdxD n k).val ∈ t ∧ (rootIdxD n k).val + 1 ∈ t) :
    ∀ k ∈ I, rootIdxD n k ∈ supportOf t ∧ rootIdxD' n k ∈ supportOf t := fun k hk =>
  ⟨mem_supportOf.2 (ht k hk).1, mem_supportOf.2 (by rw [val_rootIdxD' n hn k]; exact (ht k hk).2)⟩

end Signs

section Combine

variable {n : ℕ} {F : Type} [Field F]

theorem isCyclic_of_isPGroup_five_leviM_of_no_orth [Finite F] [CharP F 2] {f : ℕ} (hf : Odd f)
    (hFf : Nat.card F = 2 ^ f) (hn : 3 ≤ n) {I : Set (Fin n)}
    (hI : ¬ ∃ a ∈ I, ∃ b ∈ I, ∃ d ∈ I, a ≠ b ∧ a ≠ d ∧ b ≠ d ∧ cartanD n a b = 0 ∧
      cartanD n a d = 0 ∧ cartanD n b d = 0)
    (P : Subgroup (spinGroup (quadPlus n F))) (hP : P ≤ leviM (plusDatum n F hn) I)
    (h5 : IsPGroup 5 P) : IsCyclic P := by
  classical
  by_cases hends : (∃ a ∈ I, a.val + 2 = n) ∧ ∃ b ∈ I, b.val + 1 = n
  · obtain ⟨⟨a, ha, ha'⟩, ⟨b, hb, hb'⟩⟩ := hends
    have hSI := rootIdx_mem_supportOf (n := n) (by omega) (I := I)
      (t := {n - 3, n - 2, n - 1}) (fun k hk => by
        have := le_add_three_of_ends I hI ha hb ha' hb' hk
        simp only [val_rootIdxD, Finset.mem_insert, Finset.mem_singleton]
        split_ifs <;> omega)
    have hS : (supportOf (n := n) ({n - 3, n - 2, n - 1} : Finset ℕ)).card ≤ 3 :=
      (card_supportOf_le _).trans Finset.card_le_three
    refine isCyclic_of_isPGroup_five_leviM hf hFf hn
      (S := supportOf ({n - 3, n - 2, n - 1} : Finset ℕ)) (T₁ := (supportOf
        ({n - 3, n - 2, n - 1} : Finset ℕ)).disjSum (supportOf ({n - 3, n - 2, n - 1} : Finset ℕ)))
      (T₂ := ∅) hSI (fun k hk => balanced_disjSum (hSI k hk).1 (hSI k hk).2)
      (fun k _ => balanced_empty k) (fun z hz => hz.elim)
      (fun z hz => Or.inl (mem_disjSum_iff.2 hz)) ?_ P hP h5
    rw [Finset.card_disjSum]
    omega
  · obtain ⟨t, ht, htI⟩ := exists_support I hI
    have hSI := rootIdx_mem_supportOf (n := n) (by omega) htI
    have hS : (supportOf (n := n) t).card ≤ 6 := (card_supportOf_le t).trans ht
    let hB : Prop := ∃ b ∈ I, b.val + 1 = n
    let sg : Fin n → Bool := fun m => decide (¬ (m.val + 1 = n ∧ hB))
    have hsign : ∀ k ∈ I, sg (rootIdxD n k) = true ↔ sg (rootIdxD' n k) = !rootSignD n k := by
      intro k hk
      simp only [sg, decide_eq_true_eq, val_rootIdxD' n (by omega : 2 ≤ n), rootSignD]
      by_cases hk1 : k.val + 1 < n
      · have h1 : (rootIdxD n k).val = k.val := by simp [val_rootIdxD, hk1]
        have h2 : decide (n ≤ k.val + 1) = false := decide_eq_false (by omega)
        rw [h1, h2]
        simp only [Bool.not_false, decide_eq_true_eq]
        constructor
        · rintro -
          rintro ⟨h3, hB'⟩
          exact hends ⟨⟨k, hk, by omega⟩, hB'⟩
        · rintro -
          rintro ⟨h3, -⟩
          omega
      · have h1 : (rootIdxD n k).val = n - 2 := by simp [val_rootIdxD, hk1]
        have h2 : decide (n ≤ k.val + 1) = true := decide_eq_true (by omega)
        rw [h1, h2]
        simp only [Bool.not_true, decide_eq_false_iff_not, not_not]
        constructor
        · rintro -
          exact ⟨by omega, ⟨k, hk, by omega⟩⟩
        · rintro -
          rintro ⟨h3, -⟩
          omega
    have hbal : ∀ k ∈ I, Balanced (signSet (supportOf t) sg : Set (Fin n ⊕ Fin n)) k :=
      fun k hk => balanced_signSet (hSI k hk).1 (hSI k hk).2 (hsign k hk)
    refine isCyclic_of_isPGroup_five_leviM hf hFf hn (S := supportOf t)
      (T₁ := signSet (supportOf t) sg)
      (T₂ := Sum.swap '' (signSet (supportOf t) sg : Set (Fin n ⊕ Fin n))) hSI hbal
      (fun k hk => (hbal k hk).swap) ?_ ?_ ?_ P hP h5
    · rintro z ⟨w, hw, rfl⟩
      simpa using hw
    · intro z hz
      exact mem_signSet_or_swap sg hz
    · exact (card_signSet_le _ sg).trans (hS.trans (by norm_num))

end Combine

section Torus

variable {n : ℕ} {F : Type} [Field F]

theorem torusD_ne_one (hn : 3 ≤ n) (k : Fin n) {τ : Fˣ} (hτ : τ ≠ 1) :
    torusD F hn k τ ≠ 1 := by
  intro h
  have h1 := spinAction_torusD F hn k τ (rootIdxD n k) true
  rw [h, map_one] at h1
  have hc : longCoroot (rootIdxD n k) (rootIdxD' n k) true (rootSignD n k) (rootIdxD n k) true =
      1 := by
    simp [longCoroot, rootIdxD_ne n (by omega) k]
  rw [hc, zpow_one] at h1
  have := congrFun h1 (.inl (rootIdxD n k))
  simp only [plusVec, LinearEquiv.coe_one, id_eq, Pi.single_eq_same, Pi.smul_apply, smul_eq_mul,
    mul_one] at this
  exact hτ (Units.ext this.symm)

theorem ker_spinToStatedProj_eq_bot [CharP F 2] (hn : 3 ≤ n) :
    (spinToStatedProj (quadPlus n F) (range_spinMatrix_quadPlus hn)).ker = ⊥ := by
  rw [(spinToStatedProj_quadPlus hn).2.1, eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_comap, CFSG.ClassicalGroups.Orthogonal.mem_statedScalars_iff,
    toLinEquiv_spinMatrix] at hx
  obtain ⟨c, hc⟩ := CFSG.ClassicalGroups.Orthogonal.mem_scalars.mp hx
  have hQ : quadPlus n F (Pi.single (.inl ⟨0, by omega⟩) 1 + Pi.single (.inr ⟨0, by omega⟩) 1) =
      1 := by
    rw [quadPlus_apply]
    simp [Pi.single_apply]
  have hc2 : c * c = 1 := by
    have h := map_spinAction (quadPlus n F) x
      (Pi.single (.inl ⟨0, by omega⟩) 1 + Pi.single (.inr ⟨0, by omega⟩) 1)
    rw [hc, QuadraticMap.map_smul, hQ] at h
    simpa using h
  have hc1 : c = 1 := by
    have h2 : (c - 1) ^ 2 = 0 := by
      linear_combination hc2 - c * CharTwo.two_eq_zero (R := F) + CharTwo.two_eq_zero (R := F)
    exact sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
  have hx1 : x ∈ (spinAction (quadPlus n F)).ker := by
    rw [MonoidHom.mem_ker]
    exact LinearEquiv.ext fun v => by rw [hc, hc1, one_smul]; rfl
  rw [← ker_spinMatrix, ker_spinMatrix_quadPlus_eq_bot CharTwo.two_eq_zero] at hx1
  exact hx1

end Torus

section Main

local notation "A₅" => alternatingGroup (Fin 5)

theorem three_le_pRank_spinPlus {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    (hn : 4 ≤ n) {Y : Type} [Group Y] [Finite Y]
    (e : Y ≃* StatedProj (StatedOmega (StatedQuadPlus n F))) {X : Type} [Group X] [Finite X]
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hρker : ρ.ker ≤ Subgroup.center X)
    (hρ3 : Nat.Coprime 3 (Nat.card ρ.ker)) (T : Sylow 2 Y) (J : Subgroup Y)
    (hNJ : Subgroup.normalizer ((T : Subgroup Y) : Set Y) ≤ J) (hJ : J ≠ ⊤)
    (hQ : LeviSection.HasSubquotient J (A₅ × A₅)) : 3 ≤ CFSG.Open.pRank 3 (J.comap ρ) := by
  classical
  have _ := hJ
  have hn3 : 3 ≤ n := by omega
  have := Fintype.ofFinite F
  have : NeZero n := ⟨by omega⟩
  have : Finite (spinGroup (quadPlus n F)) :=
    finite_spinGroup_of_ker _ (coe_ker_spinMatrix_quadPlus (n := n) (K := F))
  obtain ⟨f, -, hf⟩ := FiniteField.card F 2
  have hfc : Nat.card F = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
  have hb := borelQuotient_spinPlus hn3 e
  obtain ⟨π', hb', hker', hBJ⟩ := BorelQuotient.exists_conj_parab hb T hNJ
  have hM := hasSubquotient_leviM_of_parab hb' hBJ hQ
  have hr : ∀ i, ParabRealThree.HasRealOrderThree (plusDatum n F hn3) i := fun i =>
    ParabRealThree.HasSL2Node.hasRealOrderThree (hasSL2Node_spinPlus hn3 i)
  rcases Nat.even_or_odd (f : ℕ) with hfe | hfo
  ·
    obtain ⟨k, hk⟩ := hfe
    have hq : Nat.card F = 4 ^ k := by rw [hfc, hk, ← two_mul, pow_mul]; norm_num
    have hq3 : 3 ∣ Nat.card F - 1 := by
      rw [hq]
      simpa using Nat.sub_dvd_pow_sub_pow 4 1 k
    obtain ⟨ω, hω⟩ : ∃ ω : Fˣ, orderOf ω = 3 := by
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have h : 3 ∣ Nat.card Fˣ := by rw [Nat.card_units]; exact hq3
      exact exists_prime_orderOf_dvd_card' 3 h
    have hω3 : ω ^ 3 = 1 := by rw [← hω, pow_orderOf_eq_one]
    have hω1 : ω ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hω
      omega
    have hker0 : (e.symm.toMonoidHom.comp
        (spinToStatedProj (quadPlus n F) (range_spinMatrix_quadPlus hn3))).ker = ⊥ := by
      rw [MonoidHom.ker_comp_of_injective _ _ e.symm.injective, ker_spinToStatedProj_eq_bot hn3]
    have hπ3 : Nat.Coprime 3 (Nat.card π'.ker) := by
      rw [hker', hker0]
      simp
    have hg3 : ∀ i : Fin n, torusD F hn3 i ω ^ 3 = 1 := fun i => by
      rw [← map_pow, hω3, map_one]
    let a : Fin n := ⟨0, by omega⟩
    let b : Fin n := ⟨1, by omega⟩
    let c : Fin n := ⟨2, by omega⟩
    refine (three_le_pRank_of_torus hb'.extras hπ3 hBJ (a := a) (b := b) (c := c)
      (fun h => absurd (congrArg Fin.val h) (by simp [a, b]))
      (fun h => absurd (congrArg Fin.val h) (by simp [a, c]))
      (fun h => absurd (congrArg Fin.val h) (by simp [b, c])) (x := torusD F hn3 a ω)
      (y := torusD F hn3 b ω) (z := torusD F hn3 c ω) ⟨ω, rfl⟩ ⟨ω, rfl⟩ ⟨ω, rfl⟩ (hg3 a) (hg3 b)
      (hg3 c) (torusD_ne_one hn3 a hω1) (torusD_ne_one hn3 b hω1)
      (torusD_ne_one hn3 c hω1)).trans (pRank_le_pRank_comap_of_coprime hρ hρ3 J)
  · by_cases ho : ∃ a ∈ negIndices (plusDatum n F hn3) (J.comap π'),
        ∃ b ∈ negIndices (plusDatum n F hn3) (J.comap π'),
        ∃ c ∈ negIndices (plusDatum n F hn3) (J.comap π'), a ≠ b ∧ a ≠ c ∧ b ≠ c ∧
          cartanD n a b = 0 ∧ cartanD n a c = 0 ∧ cartanD n b c = 0
    · obtain ⟨a, ha, b, hb2, c, hc, hab, hac, hbc, cab, cac, cbc⟩ := ho
      exact three_le_pRank_of_orth hb'.extras hb'.ker_central ρ hρ hρker hBJ hr hab hac hbc cab
        cac cbc ha hb2 hc
    · exfalso
      have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
      exact hM.false_of_isCyclic (fun P hP h5 =>
        isCyclic_of_isPGroup_five_leviM_of_no_orth hfo hfc hn3 ho P hP h5)
        LeviSection.exists_not_isCyclic_five

end Main

end CFSG.AGLEmbeddingD2.SquareSpinPlus
