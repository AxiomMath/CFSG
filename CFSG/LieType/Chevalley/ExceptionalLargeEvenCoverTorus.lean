module

public import CFSG.LieType.Chevalley.RankOneCentralImage
public import CFSG.LieType.Chevalley.HeightSeries
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteLinearized

public noncomputable section

namespace CFSG.LieType.Chevalley.ExceptionalCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem torusEltHom_commute :
    Pairwise fun i j => ∀ (x y : Kˣ), Commute (torusEltHom τ K i x) (torusEltHom τ K j y) :=
  fun i j _ x y => torusElt_mul_comm i j x y

variable (τ K) in
@[expose] def torusVec
    : (Fin τ.rank → Kˣ) →* ModGL τ K :=
  MonoidHom.noncommPiCoprod (fun k => torusEltHom τ K k) torusEltHom_commute

theorem torusVec_mulSingle
    (k : Fin τ.rank) (s : Kˣ) :
    torusVec τ K (Pi.mulSingle k s) = torusElt τ K k s := by
  rw [torusVec, MonoidHom.noncommPiCoprod_mulSingle]
  rfl

theorem torusVec_induction {P : (Fin τ.rank → Kˣ) → Prop} (h1 : P 1)
    (hmul : ∀ t t', P t → P t' → P (t * t')) (hsingle : ∀ k s, P (Pi.mulSingle k s))
    (t : Fin τ.rank → Kˣ) : P t := by
  classical
  let S : Submonoid (Fin τ.rank → Kˣ) :=
    { carrier := {t | P t}
      mul_mem' := fun ht ht' => hmul _ _ ht ht'
      one_mem' := h1 }
  rw [← Finset.univ_prod_mulSingle t]
  exact Submonoid.prod_mem S fun k _ => hsingle k (t k)

theorem torusVec_mem_adjointGroup
    (t : Fin τ.rank → Kˣ) : torusVec τ K t ∈ adjointGroup τ K := by
  induction t using torusVec_induction with
  | h1 => rw [map_one]; exact one_mem _
  | hmul t t' ht ht' => rw [map_mul]; exact mul_mem ht ht'
  | hsingle k s => rw [torusVec_mulSingle]; exact torusElt_mem_adjointGroup k s

@[expose] def cartanCoord (α : Fin τ.rank → ℤ) (k : Fin τ.rank) : ℤ :=
  ∑ j, τ.cartan k j * α j

variable (K) in
@[expose] def rootChar (α : Fin τ.rank → ℤ) : (Fin τ.rank → Kˣ) →* Kˣ where
  toFun t := ∏ k, t k ^ cartanCoord α k
  map_one' := by simp
  map_mul' t t' := by
    simp only [Pi.mul_apply, mul_zpow]
    exact Finset.prod_mul_distrib

theorem rootChar_apply (α : Fin τ.rank → ℤ) (t : Fin τ.rank → Kˣ) :
    rootChar K α t = ∏ k, t k ^ cartanCoord α k :=
  rfl

theorem rootChar_mulSingle (α : Fin τ.rank → ℤ) (k : Fin τ.rank) (s : Kˣ) :
    rootChar K α (Pi.mulSingle k s) = s ^ cartanCoord α k := by
  classical
  rw [rootChar_apply, Finset.prod_eq_single k]
  · rw [Pi.mulSingle_eq_same]
  · intro j _ hj
    rw [Pi.mulSingle_eq_of_ne hj, one_zpow]
  · intro hk
    exact absurd (Finset.mem_univ k) hk

theorem torusVec_conj_pinnedX
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) (t : Fin τ.rank → Kˣ)
    (c : K) :
    torusVec τ K t * pinnedX τ K α c * (torusVec τ K t)⁻¹ =
      pinnedX τ K α ((rootChar K α t : K) * c) := by
  induction t using torusVec_induction generalizing c with
  | h1 => simp
  | hmul t t' ht ht' =>
    have e : torusVec τ K (t * t') * pinnedX τ K α c * (torusVec τ K (t * t'))⁻¹ =
        torusVec τ K t * (torusVec τ K t' * pinnedX τ K α c * (torusVec τ K t')⁻¹) *
          (torusVec τ K t)⁻¹ := by
      rw [map_mul]
      group
    rw [e, ht', ht, map_mul, Units.val_mul, mul_assoc]
  | hsingle k s =>
    rw [torusVec_mulSingle, root_torus_conjugation k hα s c, rootChar_mulSingle]
    rfl

theorem torusVec_conj_mem_rootSpan
    (t : Fin τ.rank → Kˣ) {S : Set (Fin τ.rank → ℤ)}
    (hS : ∀ α ∈ S, IsRoot τ α) {x : ModGL τ K} (hx : x ∈ rootSpan τ K S) :
    torusVec τ K t * x * (torusVec τ K t)⁻¹ ∈ rootSpan τ K S := by
  rw [rootSpan_eq_closure] at hx ⊢
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
    obtain ⟨α, hα, c, rfl⟩ := hg
    rw [torusVec_conj_pinnedX (hS α hα)]
    exact Subgroup.subset_closure ⟨α, hα, _, rfl⟩
  | one =>
    rw [mul_one, mul_inv_cancel]
    exact one_mem _
  | mul x y _ _ hx hy =>
    have e : torusVec τ K t * (x * y) * (torusVec τ K t)⁻¹ =
        torusVec τ K t * x * (torusVec τ K t)⁻¹ * (torusVec τ K t * y * (torusVec τ K t)⁻¹) := by
      group
    rw [e]
    exact mul_mem hx hy
  | inv x _ hx =>
    have e : torusVec τ K t * x⁻¹ * (torusVec τ K t)⁻¹ =
        (torusVec τ K t * x * (torusVec τ K t)⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem hx

theorem odd_card_torus [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) (hf : 1 ≤ f) :
    Odd (Nat.card (Fin τ.rank → Kˣ)) := by
  rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, Nat.card_units, hK]
  refine Odd.pow ⟨2 ^ (f - 1) - 1, ?_⟩
  have h1 : 1 ≤ 2 ^ (f - 1) := Nat.one_le_two_pow
  have h2 : 2 ^ f = 2 * 2 ^ (f - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  omega

theorem exists_orderOf_eq [Finite K] : ∃ u : Kˣ, orderOf u = Nat.card K - 1 := by
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  exact ⟨g, by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]⟩

theorem orderOf_eq_two_pow_sub_one [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) {g : Kˣ}
    (hg : orderOf g = Nat.card K - 1) : ((orderOf g : ℕ) : ℤ) = 2 ^ f - 1 := by
  rw [hg, hK, Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

theorem rootChar_ne_one [Finite K] {f : ℕ} (hK : Nat.card K = 2 ^ f) {α : Fin τ.rank → ℤ}
    (h : ∃ k, ¬ (2 ^ f - 1 : ℤ) ∣ cartanCoord α k) : rootChar K α ≠ 1 := by
  intro h1
  obtain ⟨k, hk⟩ := h
  obtain ⟨g, hg⟩ := exists_orderOf_eq (K := K)
  have h0 : g ^ cartanCoord α k = 1 := by
    rw [← rootChar_mulSingle, h1, MonoidHom.one_apply]
  rw [← orderOf_dvd_iff_zpow_eq_one, orderOf_eq_two_pow_sub_one hK hg] at h0
  exact hk h0

theorem rootChar_form_eq_zero [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) {α β : Fin τ.rank → ℤ}
    (hnd : ∀ i j : ℕ, i < f → j < f →
      ¬ ∀ k, (2 ^ f - 1 : ℤ) ∣ 2 ^ i * cartanCoord α k + 2 ^ j * cartanCoord β k)
    (F : K → K → ZMod 2) (hF₁ : ∀ c₁ c₂ d, F (c₁ + c₂) d = F c₁ d + F c₂ d)
    (hF₂ : ∀ c d₁ d₂, F c (d₁ + d₂) = F c d₁ + F c d₂)
    (hFT : ∀ (t : Fin τ.rank → Kˣ) c d,
      F ((rootChar K α t : K) * c) ((rootChar K β t : K) * d) = F c d) :
    ∀ c d, F c d = 0 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let ι : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hι : Function.Injective ι := ι.injective
  let G : K →+ K →+ K := AddMonoidHom.mk'
    (fun c => AddMonoidHom.mk' (fun d => ι (F c d)) fun d₁ d₂ => by rw [hF₂, map_add])
    fun c₁ c₂ => by
      ext d
      simp only [AddMonoidHom.mk'_apply, AddMonoidHom.add_apply]
      rw [hF₁, map_add]
  have hG : ∀ c d, G c d = ι (F c d) := fun _ _ => rfl
  obtain ⟨-, h2, -⟩ := CFSG.LocalAnalysis.ComponentInitial.finite_field_linearized_map_bases
    Nat.prime_two hf hK
  obtain ⟨A, hA, hAuniq⟩ := h2 G
  have hcoef : ∀ (t : Fin τ.rank → Kˣ) (i j : Fin f),
      A i j * ((rootChar K α t : K) ^ 2 ^ (i : ℕ) * (rootChar K β t : K) ^ 2 ^ (j : ℕ)) =
        A i j := by
    intro t
    have huniq := hAuniq
      (fun i j => A i j * ((rootChar K α t : K) ^ 2 ^ (i : ℕ) *
        (rootChar K β t : K) ^ 2 ^ (j : ℕ))) fun x y => by
      have h1 : G x y = G ((rootChar K α t : K) * x) ((rootChar K β t : K) * y) := by
        rw [hG, hG, hFT]
      rw [h1, hA]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, mul_pow]
      ring
    intro i j
    exact congrFun (congrFun huniq i) j
  have hA0 : ∀ i j, A i j = 0 := by
    intro i j
    by_contra hne
    have key : ∀ t : Fin τ.rank → Kˣ, ((rootChar K α t ^ 2 ^ (i : ℕ) *
        rootChar K β t ^ 2 ^ (j : ℕ) : Kˣ) : K) = 1 := fun t => by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      exact (mul_eq_left₀ hne).1 (hcoef t i j)
    obtain ⟨g, hg⟩ := exists_orderOf_eq (K := K)
    refine hnd i j i.2 j.2 fun k => ?_
    have h := key (Pi.mulSingle k g)
    rw [rootChar_mulSingle, rootChar_mulSingle] at h
    rw [← orderOf_eq_two_pow_sub_one hK hg, orderOf_dvd_iff_zpow_eq_one, zpow_add,
      mul_comm ((2 : ℤ) ^ (i : ℕ)), mul_comm ((2 : ℤ) ^ (j : ℕ)), zpow_mul, zpow_mul]
    exact_mod_cast Units.val_eq_one.1 h
  intro c d
  have h0 : G c d = 0 := by
    rw [hA]
    simp [hA0]
  exact hι (by rw [map_zero, ← hG]; exact h0)

end CFSG.LieType.Chevalley.ExceptionalCover
