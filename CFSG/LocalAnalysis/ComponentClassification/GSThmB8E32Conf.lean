module

public import CFSG.LocalAnalysis.ComponentClassification.GSThmB8S6Model
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedLayerOrbitLocation
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.ComponentClassification.GSThmB

open CFSG Subgroup CFSG.ComponentClassification.UnbalancedLayer

namespace Eight

variable {X : Type} [Group X]

abbrev Eof (c : Fin 6 → X) : Subgroup X := closure (Set.range c)

abbrev E0of (c : Fin 6 → X) : Subgroup X := closure {x | ∃ i j : Fin 6, x = c i * c j}

structure E32Base (X : Type) [Group X] [Finite X] where
  c : Fin 6 → X
  c_sq : ∀ i, c i * c i = 1
  c_comm : ∀ i j, c i * c j = c j * c i
  c_five : c 5 = c 0 * c 1 * c 2 * c 3 * c 4
  card_E : Nat.card (Eof c) = 32
  π : ↥(normalizer ((Eof c : Subgroup X) : Set X)) →* Equiv.Perm (Fin 6)
  π_conj : ∀ (n : ↥(normalizer ((Eof c : Subgroup X) : Set X))) (i : Fin 6),
    (n : X) * c i * (n : X)⁻¹ = c (π n i)

structure E32Conf (X : Type) [Group X] [Finite X] extends E32Base X where
  U : Subgroup X
  U_sylow : ∃ T : Sylow 2 X, (T : Subgroup X) = U
  c_mem : ∀ i, c i ∈ U
  π_W : ∀ n : ↥(normalizer ((Eof c : Subgroup X) : Set X)), (n : X) ∈ U → π n ∈ S6M.Wlist
  π_W_onto : ∀ t ∈ S6M.Wlist, ∃ n : ↥(normalizer ((Eof c : Subgroup X) : Set X)),
    (n : X) ∈ U ∧ π n = t
  π_ker : ∀ n : ↥(normalizer ((Eof c : Subgroup X) : Set X)), (n : X) ∈ U → π n = 1 →
    (n : X) ∈ Eof c
  W_ne : U ⊓ normalizer ((Eof c : Subgroup X) : Set X) ≠ U
  fus_a : ∀ n : ↥(normalizer ((Eof c : Subgroup X) : Set X)), (n : X) ∈ U → (n : X) * n = 1 →
    (π n).IsSwap → ∃ e ∈ Eof c, e * n * (e * n) = 1 ∧
      ∀ (g : X), ∀ e' ∈ Eof c, g⁻¹ * (e * n) * g ≠ e'
  fus_z : ∀ e ∈ E0of c, e ≠ 1 → ∀ (g : X) (n : ↥(normalizer ((Eof c : Subgroup X) : Set X))),
    (n : X) = g⁻¹ * e * g → (n : X) ∈ U → ¬ (π n).IsSwap
  fus_sc : ∀ e ∈ E0of c, ∀ g : X, g⁻¹ * e * g ∈ Eof c → g⁻¹ * e * g ∈ E0of c
  sq : c 4 ∈ closure {y : X | ∃ g : X, y = g ^ 2}

@[expose] def zmod2Hom (g : X) (hg : g * g = 1) : Multiplicative (ZMod 2) →* X where
  toFun x := g ^ (Multiplicative.toAdd x).val
  map_one' := by simp
  map_mul' x y := by
    rcases S6M.zmod2_cases (Multiplicative.toAdd x) with hx | hx <;>
      rcases S6M.zmod2_cases (Multiplicative.toAdd y) with hy | hy <;>
      simp only [toAdd_mul, hx, hy]
    · simp
    · simp
    · simp
    · rw [show (1 + 1 : ZMod 2) = 0 from rfl]
      simp [ZMod.val_one, hg]

@[expose] def evenSub : Subgroup (Multiplicative S6M.V5) where
  carrier := {v | S6M.IsEven (Multiplicative.toAdd v)}
  mul_mem' {v w} hv hw := by
    show ∑ i, (Multiplicative.toAdd v + Multiplicative.toAdd w) i = 0
    rw [Finset.sum_congr rfl (fun i _ => Pi.add_apply _ _ i), Finset.sum_add_distrib,
      show ∑ i, Multiplicative.toAdd v i = 0 from hv,
      show ∑ i, Multiplicative.toAdd w i = 0 from hw, add_zero]
  one_mem' := by
    show ∑ i, (0 : S6M.V5) i = 0
    simp
  inv_mem' {v} hv := by
    show ∑ i, (-Multiplicative.toAdd v) i = 0
    rw [show (-Multiplicative.toAdd v) = Multiplicative.toAdd v from
      funext fun i => ZMod.neg_eq_self_mod_two _]
    exact hv

namespace E32Base

variable {X : Type} [Group X] [Finite X] (C : E32Base X)

abbrev E : Subgroup X := Eof C.c

abbrev E0 : Subgroup X := E0of C.c

abbrev N : Subgroup X := normalizer ((C.E : Subgroup X) : Set X)

theorem c_mem_E (i : Fin 6) : C.c i ∈ C.E := subset_closure ⟨i, rfl⟩

@[expose] noncomputable def θ0 : (Fin 5 → Multiplicative (ZMod 2)) →* X :=
  MonoidHom.noncommPiCoprod (fun i => zmod2Hom (C.c i.castSucc) (C.c_sq _)) (by
    intro i j _ x y
    exact Commute.pow_pow (C.c_comm _ _) _ _)

@[expose] noncomputable def θ (v : S6M.V5) : X := C.θ0 fun i => Multiplicative.ofAdd (v i)

theorem θ_add (v w : S6M.V5) : C.θ (v + w) = C.θ v * C.θ w := by
  rw [θ, θ, θ, ← map_mul]
  rfl

theorem θ_zero : C.θ 0 = 1 := by
  rw [θ]
  exact map_one _

@[expose] noncomputable def θhom : Multiplicative S6M.V5 →* X where
  toFun v := C.θ (Multiplicative.toAdd v)
  map_one' := C.θ_zero
  map_mul' _ _ := C.θ_add _ _

theorem θ_single (i : Fin 5) : C.θ (Pi.single i 1) = C.c i.castSucc := by
  have h : (fun j => Multiplicative.ofAdd ((Pi.single i (1 : ZMod 2) : S6M.V5) j)) =
      Pi.mulSingle i (Multiplicative.ofAdd (1 : ZMod 2)) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp
    · rw [Pi.single_eq_of_ne hj, Pi.mulSingle_eq_of_ne hj]
      rfl
  rw [θ, h, θ0, MonoidHom.noncommPiCoprod_mulSingle]
  show C.c i.castSucc ^ (1 : ZMod 2).val = C.c i.castSucc
  rw [ZMod.val_one, pow_one]

theorem ehat_five : S6M.ehat 5 = fun _ => 1 := by decide

theorem θ_ehat (j : Fin 6) : C.θ (S6M.ehat j) = C.c j := by
  rcases Fin.eq_castSucc_or_eq_last j with ⟨i, rfl⟩ | rfl
  · rw [S6M.ehat_castSucc, θ_single]
  · have h1 : (fun _ => 1 : S6M.V5) = Pi.single 0 1 + Pi.single 1 1 + Pi.single 2 1 +
        Pi.single 3 1 + Pi.single 4 1 := by decide
    rw [show (Fin.last 5 : Fin 6) = 5 from rfl, ehat_five, h1, θ_add, θ_add, θ_add, θ_add,
      θ_single, θ_single, θ_single, θ_single, θ_single, C.c_five]
    rfl

theorem θ_mem (v : S6M.V5) : C.θ v ∈ C.E := by
  have h : v = ∑ i : Fin 5, Pi.single i (v i) := (Finset.univ_sum_single v).symm
  have key : ∀ (s : Finset (Fin 5)), C.θ (∑ i ∈ s, Pi.single i (v i)) ∈ C.E := by
    intro s
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, θ_zero]; exact one_mem _
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, θ_add]
      refine mul_mem ?_ ih
      rcases S6M.zmod2_cases (v i) with h0 | h0 <;> rw [h0]
      · rw [Pi.single_zero, θ_zero]
        exact one_mem _
      · rw [θ_single]
        exact C.c_mem_E _
  rw [h]
  exact key _

theorem mem_E_iff {e : X} : e ∈ C.E ↔ ∃ v, C.θ v = e := by
  constructor
  · intro he
    have hle : C.E ≤ C.θhom.range := by
      rw [closure_le]
      rintro _ ⟨j, rfl⟩
      exact ⟨Multiplicative.ofAdd (S6M.ehat j), C.θ_ehat j⟩
    obtain ⟨v, hv⟩ := hle he
    exact ⟨Multiplicative.toAdd v, hv⟩
  · rintro ⟨v, rfl⟩
    exact C.θ_mem v

theorem θ_injective : Function.Injective C.θ := by
  set f : S6M.V5 → ↥C.E := fun v => ⟨C.θ v, C.θ_mem v⟩ with hf
  have hsurj : Function.Surjective f := by
    rintro ⟨e, he⟩
    obtain ⟨v, rfl⟩ := C.mem_E_iff.mp he
    exact ⟨v, rfl⟩
  have hcard : Nat.card S6M.V5 ≤ Nat.card ↥C.E := by
    rw [C.card_E, Nat.card_eq_fintype_card, Fintype.card_fun, ZMod.card, Fintype.card_fin]
    norm_num
  intro v w hvw
  exact (hsurj.bijective_of_nat_card_le hcard).1 (Subtype.ext hvw)

theorem θ_inj_iff {v w : S6M.V5} : C.θ v = C.θ w ↔ v = w :=
  ⟨fun h => C.θ_injective h, fun h => h ▸ rfl⟩

theorem θ_eq_one_iff {v : S6M.V5} : C.θ v = 1 ↔ v = 0 := by
  rw [← C.θ_zero, θ_inj_iff]

theorem c_injective : Function.Injective C.c := by
  intro i j hij
  rw [← C.θ_ehat, ← C.θ_ehat, θ_inj_iff] at hij
  revert hij
  revert i j
  decide

theorem θ_conj (n : ↥C.N) (v : S6M.V5) :
    (n : X) * C.θ v * (n : X)⁻¹ = C.θ (S6M.act (C.π n) v) := by
  have h : v = ∑ i : Fin 5, Pi.single i (v i) := (Finset.univ_sum_single v).symm
  have key : ∀ (s : Finset (Fin 5)), (n : X) * C.θ (∑ i ∈ s, Pi.single i (v i)) * (n : X)⁻¹ =
      C.θ (S6M.act (C.π n) (∑ i ∈ s, Pi.single i (v i))) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, θ_zero, S6M.act_zero, θ_zero]
      group
    | insert i s hi ih =>
      rw [Finset.sum_insert hi, θ_add, S6M.act_add, θ_add, ← ih]
      rw [show (n : X) * (C.θ (Pi.single i (v i)) * C.θ (∑ i ∈ s, Pi.single i (v i))) *
          (n : X)⁻¹ = ((n : X) * C.θ (Pi.single i (v i)) * (n : X)⁻¹) *
          ((n : X) * C.θ (∑ i ∈ s, Pi.single i (v i)) * (n : X)⁻¹) by group]
      congr 1
      rcases S6M.zmod2_cases (v i) with h0 | h0 <;> rw [h0]
      · rw [Pi.single_zero, θ_zero, S6M.act_zero, θ_zero]
        group
      · rw [θ_single, C.π_conj, ← S6M.ehat_castSucc, S6M.act_ehat, θ_ehat]
  rw [h]
  exact key _

theorem comm_iff (n : ↥C.N) (v : S6M.V5) :
    (n : X) * C.θ v = C.θ v * n ↔ S6M.act (C.π n) v = v := by
  rw [← C.θ_inj_iff, ← C.θ_conj]
  constructor
  · intro h
    rw [h, mul_inv_cancel_right]
  · intro h
    calc (n : X) * C.θ v = (n : X) * C.θ v * (n : X)⁻¹ * n := by group
      _ = C.θ v * n := by rw [h]

theorem E_comm {x y : X} (hx : x ∈ C.E) (hy : y ∈ C.E) : x * y = y * x := by
  obtain ⟨v, rfl⟩ := C.mem_E_iff.mp hx
  obtain ⟨w, rfl⟩ := C.mem_E_iff.mp hy
  rw [← θ_add, ← θ_add, add_comm]

theorem π_E {e : ↥C.N} (he : (e : X) ∈ C.E) : C.π e = 1 := by
  refine Equiv.ext fun i => ?_
  have h1 := C.π_conj e i
  rw [C.E_comm he (C.c_mem_E i), mul_inv_cancel_right] at h1
  rw [Equiv.Perm.one_apply]
  exact (C.c_injective h1).symm

theorem ehat_add_even (i j : Fin 6) : S6M.IsEven (S6M.ehat i + S6M.ehat j) := by
  rw [← S6M.isEvenB_iff]
  revert i j
  decide

theorem even_decomp : (S6M.allV.all fun v => !S6M.isEvenB v || S6M.veq v
    (v 0 • (S6M.ehat 0 + S6M.ehat 4) + v 1 • (S6M.ehat 1 + S6M.ehat 4) +
      v 2 • (S6M.ehat 2 + S6M.ehat 4) + v 3 • (S6M.ehat 3 + S6M.ehat 4))) = true := by
  decide +kernel

theorem θ_smul_mem (x : ZMod 2) (i j : Fin 6) : C.θ (x • (S6M.ehat i + S6M.ehat j)) ∈ C.E0 := by
  rcases S6M.zmod2_cases x with rfl | rfl
  · rw [zero_smul, θ_zero]
    exact one_mem _
  · rw [one_smul, θ_add, θ_ehat, θ_ehat]
    exact subset_closure ⟨i, j, rfl⟩

theorem mem_E0_iff {e : X} : e ∈ C.E0 ↔ ∃ v, S6M.IsEven v ∧ C.θ v = e := by
  constructor
  · intro he
    have hle : C.E0 ≤ evenSub.map C.θhom := by
      rw [closure_le]
      rintro _ ⟨i, j, rfl⟩
      exact ⟨Multiplicative.ofAdd (S6M.ehat i + S6M.ehat j), ehat_add_even i j, by
        show C.θ (S6M.ehat i + S6M.ehat j) = _
        rw [θ_add, θ_ehat, θ_ehat]⟩
    obtain ⟨v, hv, hve⟩ := hle he
    exact ⟨Multiplicative.toAdd v, hv, hve⟩
  · rintro ⟨v, hv, rfl⟩
    have h1 := List.all_eq_true.mp even_decomp v (S6M.mem_allV v)
    rw [Bool.or_eq_true, Bool.not_eq_true', S6M.isEvenB_iff.mpr hv] at h1
    have h2 := S6M.veq_iff.mp (h1.resolve_left (by simp))
    rw [h2, θ_add, θ_add, θ_add]
    exact mul_mem (mul_mem (mul_mem (C.θ_smul_mem _ _ _) (C.θ_smul_mem _ _ _))
      (C.θ_smul_mem _ _ _)) (C.θ_smul_mem _ _ _)

theorem E0_le_E : C.E0 ≤ C.E := fun e he => by
  obtain ⟨v, -, rfl⟩ := C.mem_E0_iff.mp he
  exact C.θ_mem v

theorem card_le_length {A : Subgroup X} (p : S6M.V5 → Bool)
    (hA : ∀ a ∈ A, ∃ v, p v = true ∧ C.θ v = a) : Nat.card A ≤ (S6M.allV.filter p).length := by
  rw [← S6M.ncard_eq_length, ← Nat.card_coe_set_eq]
  calc Nat.card ↥(A : Set X) = (A : Set X).ncard := Nat.card_coe_set_eq _
    _ ≤ (C.θ '' {v | p v = true}).ncard := by
        refine Set.ncard_le_ncard (fun a ha => ?_) (Set.toFinite _)
        obtain ⟨v, hv, rfl⟩ := hA a ha
        exact ⟨v, hv, rfl⟩
    _ ≤ {v : S6M.V5 | p v = true}.ncard := Set.ncard_image_le (Set.toFinite _)

end E32Base

namespace E32Conf

variable {X : Type} [Group X] [Finite X] (C : E32Conf X)

abbrev W : Subgroup X := C.U ⊓ C.N

theorem E_le_U : C.E ≤ C.U := (closure_le _).mpr fun _ ⟨i, hi⟩ => hi ▸ C.c_mem i

theorem E_le_W : C.E ≤ C.W := le_inf C.E_le_U le_normalizer

theorem π_mem_W {n : X} (hn : n ∈ C.W) : C.π ⟨n, hn.2⟩ ∈ S6M.Wlist := C.π_W _ hn.1

end E32Conf

end Eight

end CFSG.ComponentClassification.GSThmB
