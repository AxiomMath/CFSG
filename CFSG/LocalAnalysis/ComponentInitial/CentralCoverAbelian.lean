module

public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverSylow
public import CFSG.LocalAnalysis.ComponentInitial.LiftOddQuotient

public section

namespace CFSG.LocalAnalysis.ComponentInitial

open Subgroup CFSG.ComponentClassification
open scoped commutatorElement

variable {G : Type*} [Group G]

theorem commutatorElement_mul_left_of_mem_center {a b c : G} (h : ⁅b, c⁆ ∈ center G) :
    ⁅a * b, c⁆ = ⁅a, c⁆ * ⁅b, c⁆ := by
  have hz := mem_center_iff.1 h
  have h1 : ⁅a * b, c⁆ = a * ⁅b, c⁆ * (c * a⁻¹ * c⁻¹) := by
    simp only [commutatorElement_def]; group
  have h2 : ⁅a, c⁆ = a * (c * a⁻¹ * c⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [h1, h2, mul_assoc a, ← hz (c * a⁻¹ * c⁻¹), ← mul_assoc]

theorem commutatorElement_mul_right_of_mem_center' {x y z : G}
    (hz : ⁅x, z⁆ ∈ center G) : ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  have h := mem_center_iff.1 hz
  have : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]; group
  rw [this, h y, mul_assoc ⁅x, z⁆, mul_inv_cancel, mul_one]

theorem commutatorElement_mem_closure_image2 {X : Set G}
    (hc : ∀ a ∈ closure X, ∀ b ∈ closure X, ⁅a, b⁆ ∈ center G) {a b : G}
    (ha : a ∈ closure X) (hb : b ∈ closure X) :
    ⁅a, b⁆ ∈ closure (Set.image2 (fun x y => ⁅x, y⁆) X X) := by
  set D := closure (Set.image2 (fun x y => ⁅x, y⁆) X X)
  have h1 : ∀ x ∈ X, ∀ b (hb : b ∈ closure X), ⁅x, b⁆ ∈ D := by
    intro x hx b hb
    induction hb using Subgroup.closure_induction with
    | mem y hy => exact subset_closure ⟨x, hx, y, hy, rfl⟩
    | one => simp
    | mul y z hy hz ihy ihz =>
      rw [commutatorElement_mul_right_of_mem_center' (hc x (subset_closure hx) z hz)]
      exact D.mul_mem ihy ihz
    | inv y hy ihy =>
      have hinv := commutatorElement_mul_right_of_mem_center' (y := y) (z := y⁻¹)
        (hc x (subset_closure hx) y⁻¹ (inv_mem hy))
      rw [mul_inv_cancel, commutatorElement_one_right] at hinv
      rw [eq_inv_of_mul_eq_one_right hinv.symm]
      exact D.inv_mem ihy
  induction ha using Subgroup.closure_induction with
  | mem x hx => exact h1 x hx b hb
  | one => simp
  | mul y z hy hz ihy ihz =>
    rw [commutatorElement_mul_left_of_mem_center (hc z hz b hb)]
    exact D.mul_mem ihy ihz
  | inv y hy ihy =>
    have hinv := commutatorElement_mul_left_of_mem_center (a := y) (b := y⁻¹) (c := b)
      (hc y⁻¹ (inv_mem hy) b hb)
    rw [mul_inv_cancel, commutatorElement_one_left] at hinv
    rw [eq_inv_of_mul_eq_one_right hinv.symm]
    exact D.inv_mem ihy

theorem commutatorElement_pow_left_of_mem_center {x y : G} (h : ⁅x, y⁆ ∈ center G) (n : ℕ) :
    ⁅x ^ n, y⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ', commutatorElement_mul_left_of_mem_center (by rw [ih]; exact pow_mem h n), ih,
      pow_succ']

theorem commutatorElement_pow_right_of_mem_center {x y : G} (h : ⁅x, y⁆ ∈ center G) (n : ℕ) :
    ⁅x, y ^ n⁆ = ⁅x, y⁆ ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, commutatorElement_mul_right_of_mem_center' h, ih, pow_succ]

@[expose] noncomputable def zmodHom {A : Type*} [Group A] (n : ℕ) (c : A) (hc : c ^ n = 1) :
    Multiplicative (ZMod n) →* A :=
  AddMonoidHom.toMultiplicativeLeft
    (ZMod.lift n ⟨zmultiplesHom (Additive A) (Additive.ofMul c), by
      simp only [zmultiplesHom_apply, natCast_zsmul]
      exact congrArg Additive.ofMul hc⟩)

theorem zmodHom_ofAdd_one {A : Type*} [Group A] (n : ℕ) (c : A) (hc : c ^ n = 1) :
    zmodHom n c hc (Multiplicative.ofAdd 1) = c := by
  change Additive.toMul (ZMod.lift n _ (1 : ZMod n)) = c
  rw [← Int.cast_one, ZMod.lift_coe]
  simp

theorem closure_mulSingle_eq_top {d : ℕ} (m : Fin d → ℕ) [∀ i, NeZero (m i)] :
    Subgroup.closure (Set.range fun i => (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (m i))) :
      (i : Fin d) → Multiplicative (ZMod (m i)))) = ⊤ := by
  refine eq_top_iff.2 fun f _ => ?_
  rw [← Finset.univ_prod_mulSingle f]
  refine Subgroup.prod_mem _ fun i _ => ?_
  have : Pi.mulSingle i (f i) = (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (m i))) :
      (i : Fin d) → Multiplicative (ZMod (m i))) ^ (ZMod.val (Multiplicative.toAdd (f i))) := by
    rw [← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_zmod_val, ofAdd_toAdd]
  rw [this]
  exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _

theorem perfect_central_cover_abelian_sylow_prime_kernel_bound {E Q : Type*} [Group E]
    [Group Q] [Finite E] [Finite Q] [Group.IsPerfect E] {η : E →* Q}
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    (Cℓ : Sylow ℓ η.ker) (S : Sylow ℓ Q) {d : ℕ} (a : Fin d → ℕ) (_ha : ∀ i, 1 ≤ a i)
    (hS : Nonempty ((S : Subgroup Q) ≃* ((i : Fin d) → Multiplicative (ZMod (ℓ ^ a i))))) :
    ∃ φ : ((p : {p : Fin d × Fin d // p.1 < p.2}) →
        Multiplicative (ZMod (ℓ ^ min (a p.1.1) (a p.1.2)))) →* (Cℓ : Subgroup η.ker),
      Function.Surjective φ := by
  classical
  obtain ⟨e⟩ := hS
  obtain ⟨T, hT⟩ := exists_sylow_map_eq hη S
  have hneZ : ∀ i, NeZero (ℓ ^ a i) := fun i => ⟨pow_ne_zero _ hℓ.out.ne_zero⟩
  let f : (T : Subgroup E) →* S :=
    (η.comp (T : Subgroup E).subtype).codRestrict (S : Subgroup Q) fun t => by
      rw [← hT]; exact Subgroup.mem_map_of_mem _ t.2
  have hf : Function.Surjective f := by
    rintro ⟨s, hs⟩
    have hs' := hs
    rw [← hT] at hs'
    obtain ⟨t, ht, rfl⟩ := hs'
    exact ⟨⟨t, ht⟩, rfl⟩
  have hfker : ∀ t, t ∈ f.ker ↔ (t : E) ∈ η.ker := fun t => by
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Subtype.coe_inj]
    rfl
  have hfZ : f.ker ≤ center (T : Subgroup E) := fun t ht =>
    mem_center_iff.2 fun u => Subtype.ext (mem_center_iff.1 (hC ((hfker t).1 ht)) u)
  have hScomm : ∀ s s' : S, s * s' = s' * s := fun s s' =>
    e.injective (by rw [map_mul, map_mul, mul_comm])
  have hcomm_ker : ∀ t t' : (T : Subgroup E), ⁅t, t'⁆ ∈ f.ker := fun t t' => by
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hScomm _ _
  have hnorm : (Cℓ : Subgroup η.ker).Normal := by
    refine ⟨fun x _ g => ?_⟩
    have hcomm : g * x = x * g := Subtype.ext (mem_center_iff.1 (hC x.2) g)
    rwa [hcomm, mul_inv_cancel_right]
  have hTC : ∀ t : (T : Subgroup E), ∀ ht : (t : E) ∈ η.ker,
      (⟨t, ht⟩ : η.ker) ∈ (Cℓ : Subgroup η.ker) := fun t ht => by
    refine mem_sylow_of_normal Cℓ hnorm ?_
    obtain ⟨n, hn⟩ := (T.isPGroup' t)
    obtain ⟨m, hm⟩ := CFSG.LieType.CentralExt.exists_orderOf_eq_pow_of_pow_eq_one (p := ℓ) (n := n)
      (congrArg Subtype.val hn)
    exact ⟨m, by rw [Subgroup.orderOf_mk]; exact hm⟩
  let g : Fin d → S := fun i =>
    e.symm (Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod (ℓ ^ a i))))
  choose x hx using fun i => hf (g i)
  have hcen : ∀ u ∈ closure (Set.range x), ∀ v ∈ closure (Set.range x),
      ⁅u, v⁆ ∈ center (T : Subgroup E) := fun u _ v _ => hfZ (hcomm_ker u v)
  have hW : ∀ t, ∃ w ∈ closure (Set.range x), w⁻¹ * t ∈ f.ker := by
    have hmap : (closure (Set.range x)).map f = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have hfx : f ∘ x = g := funext hx
      rw [hfx]
      have h3 := congrArg (Subgroup.map e.symm.toMonoidHom)
        (closure_mulSingle_eq_top (fun i => ℓ ^ a i))
      rw [MonoidHom.map_closure, Subgroup.map_top_of_surjective _ e.symm.surjective,
        ← Set.range_comp] at h3
      exact h3
    intro t
    have ht : f t ∈ (closure (Set.range x)).map f := by rw [hmap]; exact mem_top _
    obtain ⟨w, hw, hwt⟩ := ht
    exact ⟨w, hw, by rw [MonoidHom.mem_ker, map_mul, map_inv, hwt, inv_mul_cancel]⟩
  have hTD : commutator (T : Subgroup E) ≤
      closure (Set.image2 (fun u v => ⁅u, v⁆) (Set.range x) (Set.range x)) := by
    rw [_root_.commutator_def]
    refine (commutator_le).2 fun t _ t' _ => ?_
    obtain ⟨w, hw, hwt⟩ := hW t
    obtain ⟨w', hw', hwt'⟩ := hW t'
    have ht : t = w * (w⁻¹ * t) := by group
    have ht' : t' = w' * (w'⁻¹ * t') := by group
    rw [ht, ht', CentralExtensions.commutator_mul_center_left _ _ _ (hfZ hwt),
      CentralExtensions.commutator_mul_center_right _ _ _ (hfZ hwt')]
    exact commutatorElement_mem_closure_image2 hcen hw hw'
  have hxpow : ∀ i, x i ^ (ℓ ^ a i) ∈ f.ker := fun i => by
    rw [MonoidHom.mem_ker, map_pow, hx]
    change e.symm _ ^ _ = 1
    rw [← map_pow, ← Pi.mulSingle_pow, ← ofAdd_nsmul, nsmul_one, ZMod.natCast_self, ofAdd_zero,
      Pi.mulSingle_one, map_one]
  have hcpow : ∀ i j, ⁅x i, x j⁆ ^ (ℓ ^ min (a i) (a j)) = 1 := fun i j => by
    have hc := hcen _ (subset_closure (Set.mem_range_self i)) _
      (subset_closure (Set.mem_range_self j))
    rcases le_total (a i) (a j) with h | h
    · rw [min_eq_left h, ← commutatorElement_pow_left_of_mem_center hc,
        commutatorElement_eq_one_iff_mul_comm]
      exact (mem_center_iff.1 (hfZ (hxpow i)) (x j)).symm
    · rw [min_eq_right h, ← commutatorElement_pow_right_of_mem_center hc,
        commutatorElement_eq_one_iff_mul_comm]
      exact mem_center_iff.1 (hfZ (hxpow j)) (x i)
  let c : Fin d → Fin d → (Cℓ : Subgroup η.ker) := fun i j =>
    ⟨⟨(⁅x i, x j⁆ : (T : Subgroup E)), (hfker _).1 (hcomm_ker _ _)⟩, hTC _ _⟩
  have hc : ∀ i j, ((c i j : η.ker) : E) = ((⁅x i, x j⁆ : (T : Subgroup E)) : E) :=
    fun _ _ => rfl
  have hcpow' : ∀ i j, c i j ^ (ℓ ^ min (a i) (a j)) = 1 := fun i j => by
    apply Subtype.ext; apply Subtype.ext
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [hc, ← SubgroupClass.coe_pow, hcpow]
    rfl
  let ψ : (p : {p : Fin d × Fin d // p.1 < p.2}) →
      Multiplicative (ZMod (ℓ ^ min (a p.1.1) (a p.1.2))) →* (Cℓ : Subgroup η.ker) :=
    fun p => zmodHom _ (c p.1.1 p.1.2) (hcpow' p.1.1 p.1.2)
  have hψcomm : Pairwise fun p q => ∀ u v, Commute (ψ p u) (ψ q v) := fun _ _ _ u v =>
    Subtype.ext (Subtype.ext (by
      simp only [Subgroup.coe_mul]
      exact mem_center_iff.1 (hC (ψ _ v).1.2) _))
  refine ⟨MonoidHom.noncommPiCoprod ψ hψcomm, fun z => ?_⟩
  set φ := MonoidHom.noncommPiCoprod ψ hψcomm
  have hcφ : ∀ i j, i < j → c i j ∈ φ.range := fun i j hij =>
    ⟨Pi.mulSingle ⟨(i, j), hij⟩ (Multiplicative.ofAdd 1), by
      rw [MonoidHom.noncommPiCoprod_mulSingle]
      exact zmodHom_ofAdd_one _ _ _⟩
  have hZT : ∀ z : (Cℓ : Subgroup η.ker), ((z : η.ker) : E) ∈ (T : Subgroup E) := fun z =>
    CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow T
      ((Cℓ : Subgroup η.ker).map η.ker.subtype) (by rintro _ ⟨y, -, rfl⟩; exact hC y.2)
      (Cℓ.isPGroup'.map _) ⟨z, z.2, rfl⟩
  let ι : (Cℓ : Subgroup η.ker) →* (T : Subgroup E) :=
    ((η.ker.subtype.comp (Cℓ : Subgroup η.ker).subtype).codRestrict _ hZT)
  have hι : Function.Injective ι := fun u v h => by
    have := congrArg (fun t : (T : Subgroup E) => (t : E)) h
    exact Subtype.ext (Subtype.ext this)
  have hιc : ∀ i j, ι (c i j) = ⁅x i, x j⁆ := fun _ _ => rfl
  have hDle : closure (Set.image2 (fun u v => ⁅u, v⁆) (Set.range x) (Set.range x)) ≤
      φ.range.map ι := by
    rw [closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, _, ⟨j, rfl⟩, rfl⟩
    rcases lt_trichotomy i j with hij | rfl | hij
    · exact ⟨c i j, hcφ i j hij, hιc i j⟩
    · change ⁅x i, x i⁆ ∈ φ.range.map ι
      rw [commutatorElement_self]; exact one_mem _
    · refine ⟨(c j i)⁻¹, inv_mem (hcφ j i hij), ?_⟩
      change ι (c j i)⁻¹ = ⁅x i, x j⁆
      rw [map_inv, hιc, commutatorElement_inv]
  have hAT := CFSG.ShultStronglyClosedTI.central_pSubgroup_le_sylow_derived T
    ((Cℓ : Subgroup η.ker).map η.ker.subtype) (by rintro _ ⟨y, -, rfl⟩; exact hC y.2)
    (Cℓ.isPGroup'.map _) ⟨z, z.2, rfl⟩
  obtain ⟨t, htT, hte⟩ := hAT
  obtain ⟨v, hv, hvt⟩ := hDle (hTD htT)
  have hvz : v = z := hι (by
    rw [hvt]
    exact Subtype.ext hte)
  rw [← hvz]
  exact hv

theorem perfect_central_cover_elementary_sylow_prime_kernel_bound {E Q : Type*} [Group E]
    [Group Q] [Finite E] [Finite Q] [Group.IsPerfect E] {η : E →* Q}
    (hη : Function.Surjective η) (hC : η.ker ≤ center E) {ℓ : ℕ} [hℓ : Fact ℓ.Prime]
    (Cℓ : Sylow ℓ η.ker) (S : Sylow ℓ Q) {d : ℕ}
    (hS : Nonempty ((S : Subgroup Q) ≃* (Fin d → Multiplicative (ZMod ℓ)))) :
    CFSG.IsElementaryAbelian ℓ (Cℓ : Subgroup η.ker) ∧
      ∃ r ≤ d * (d - 1) / 2, Nat.card (Cℓ : Subgroup η.ker) = ℓ ^ r := by
  classical
  obtain ⟨e⟩ := hS
  let e' : (S : Subgroup Q) ≃* ((i : Fin d) → Multiplicative (ZMod (ℓ ^ (fun _ => 1) i))) :=
    e.trans (MulEquiv.piCongrRight fun _ =>
      (ZMod.ringEquivCongr (pow_one ℓ).symm).toAddEquiv.toMultiplicative)
  obtain ⟨φ, hφ⟩ := perfect_central_cover_abelian_sylow_prime_kernel_bound hη hC Cℓ S
    (fun _ => 1) (fun _ => le_rfl) ⟨e'⟩
  have hℓ0 : ((ℓ : ℕ) : ZMod (ℓ ^ min 1 1)) = 0 := by
    have h := ZMod.natCast_self (ℓ ^ min 1 1)
    simpa using h
  have hexp : ∀ z : (Cℓ : Subgroup η.ker), z ^ ℓ = 1 := by
    intro z
    obtain ⟨v, rfl⟩ := hφ z
    rw [← map_pow]
    have hv : v ^ ℓ = 1 := by
      funext q
      rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (v q), ← ofAdd_nsmul, nsmul_eq_mul, hℓ0,
        zero_mul, ofAdd_zero]
    rw [hv, map_one]
  refine ⟨{ is_comm := ⟨fun u v => Subtype.ext (Subtype.ext
              (mem_center_iff.1 (hC v.1.2) _))⟩
            exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hexp }, ?_⟩
  obtain ⟨r, hr⟩ := (IsPGroup.iff_card).1 Cℓ.isPGroup'
  refine ⟨r, ?_, hr⟩
  have hle := Nat.card_le_card_of_surjective φ hφ
  have hcardP : Nat.card ((p : {p : Fin d × Fin d // p.1 < p.2}) →
      Multiplicative (ZMod (ℓ ^ min ((fun _ : Fin d => 1) p.1.1) ((fun _ : Fin d => 1) p.1.2)))) =
      ℓ ^ (d * (d - 1) / 2) := by
    rw [Nat.card_pi]
    simp only [min_self, pow_one, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card, Finset.prod_const, Finset.card_univ]
    congr 1
    rw [Fintype.card_subtype, Fintype.card_product_filter_lt, Fintype.card_fin,
      Nat.choose_two_right]
  rw [hr, hcardP] at hle
  exact (Nat.pow_le_pow_iff_right hℓ.out.one_lt).1 hle

end CFSG.LocalAnalysis.ComponentInitial
