module

public import CFSG.LieType.Ree.LargeReeTorusExponents
public import CFSG.LieType.Ree.FixedSubgroupData
public import CFSG.LocalAnalysis.ComponentInitial.FieldFiniteLinearized

public noncomputable section

namespace CFSG.LieType.Ree.LargeReeCover

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley ReeTag

variable {K : Type} [Field K] (a : ℕ)

@[expose] def torusHom
    (i : Fin F4.tag.rank) : Kˣ →* ModGL F4.tag K where
  toFun := torusElt F4.tag K i
  map_one' := torusElt_one i
  map_mul' := torusElt_mul i

theorem torusElt_commute
    (i j : Fin F4.tag.rank) (t u : Kˣ) :
    Commute (torusElt F4.tag K i t) (torusElt F4.tag K j u) :=
  torusElt_mul_comm i j t u

theorem torusHom_apply
    (i : Fin F4.tag.rank) (t : Kˣ) :
    torusHom (K := K) i t = torusElt F4.tag K i t :=
  rfl

@[expose] def pairedTorusHom
    (j k : Fin F4.tag.rank) : Kˣ →* ModGL F4.tag K :=
  ((torusHom j).noncommCoprod ((torusHom k).comp (powMonoidHom (2 ^ a)))
    fun m n => by
      rw [MonoidHom.comp_apply, powMonoidHom_apply, torusHom_apply, torusHom_apply]
      exact torusElt_commute j k m _).comp ((MonoidHom.id _).prod (MonoidHom.id _))

theorem pairedTorusHom_apply
    (j k : Fin F4.tag.rank) (u : Kˣ) :
    pairedTorusHom (K := K) a j k u = torusElt F4.tag K j u * torusElt F4.tag K k (u ^ 2 ^ a) :=
  rfl

@[expose] def torusPair
    : Kˣ × Kˣ →* ModGL F4.tag K :=
  (pairedTorusHom a (f4i 0) (f4i 3)).noncommCoprod (pairedTorusHom a (f4i 1) (f4i 2))
    fun m n => by
      rw [pairedTorusHom_apply, pairedTorusHom_apply]
      exact ((torusElt_commute _ _ _ _).mul_left (torusElt_commute _ _ _ _)).mul_right
        ((torusElt_commute _ _ _ _).mul_left (torusElt_commute _ _ _ _))

theorem torusPair_apply (u v : Kˣ) :
    torusPair (K := K) a (u, v) = torusElt F4.tag K (f4i 0) u *
      torusElt F4.tag K (f4i 3) (u ^ 2 ^ a) *
        (torusElt F4.tag K (f4i 1) v * torusElt F4.tag K (f4i 2) (v ^ 2 ^ a)) :=
  rfl

theorem perm_f4i_zero : F4.perm (f4i 0) = f4i 3 := by decide

theorem perm_f4i_one : F4.perm (f4i 1) = f4i 2 := by decide

theorem f4i_zero_mem_longSet : f4i 0 ∈ F4.longSet := by decide

theorem f4i_one_mem_longSet : f4i 1 ∈ F4.longSet := by decide

theorem torusPair_eq_reeTorus
    (u v : Kˣ) :
    torusPair (K := K) a (u, v) =
      ((F4.reeTorus a (f4i 0) u * F4.reeTorus a (f4i 1) v : adjointGroup F4.tag K) :
        ModGL F4.tag K) := by
  simp only [torusPair_apply, reeTorus, Subgroup.coe_mul, perm_f4i_zero, perm_f4i_one]
  rfl

theorem torusPair_mem_reeGamma
    [Finite K] [CharP K F4.prime]
    (hK : Nat.card K = F4.prime ^ (2 * a + 1)) (t : Kˣ × Kˣ) :
    torusPair (K := K) a t ∈ F4.reeGamma K a := by
  obtain ⟨u, v⟩ := t
  rw [torusPair_eq_reeTorus, reeGamma_eq_reeFixedGroup, reeFixedGroup_eq_map_reeFixed]
  refine Subgroup.mem_map_of_mem _ (mul_mem ?_ ?_)
  · exact F4.reeTorus_mem_reeFixed a hK f4i_zero_mem_longSet u
  · exact F4.reeTorus_mem_reeFixed a hK f4i_one_mem_longSet v

@[expose] def torusWeight (β : Fin F4.tag.rank → ℤ) : Kˣ × Kˣ →* Kˣ where
  toFun t := t.1 ^ torusExp0 (2 ^ a) β * t.2 ^ torusExp1 (2 ^ a) β
  map_one' := by simp
  map_mul' t t' := by
    simp only [Prod.fst_mul, Prod.snd_mul, mul_zpow]
    exact mul_mul_mul_comm _ _ _ _

theorem torusWeight_apply (β : Fin F4.tag.rank → ℤ) (u v : Kˣ) :
    torusWeight (K := K) a β (u, v) = u ^ torusExp0 (2 ^ a) β * v ^ torusExp1 (2 ^ a) β :=
  rfl

theorem torusWeight_fst (β : Fin F4.tag.rank → ℤ) (u : Kˣ) :
    torusWeight (K := K) a β (u, 1) = u ^ torusExp0 (2 ^ a) β := by
  rw [torusWeight_apply, one_zpow, mul_one]

theorem torusWeight_snd (β : Fin F4.tag.rank → ℤ) (v : Kˣ) :
    torusWeight (K := K) a β (1, v) = v ^ torusExp1 (2 ^ a) β := by
  rw [torusWeight_apply, one_zpow, one_mul]

theorem torusPair_conj_pinnedX
    (t : Kˣ × Kˣ) {β : Fin F4.tag.rank → ℤ} (hβ : IsRoot F4.tag β)
    (c : K) :
    torusPair a t * pinnedX F4.tag K β c * (torusPair a t)⁻¹ =
      pinnedX F4.tag K β ((torusWeight a β t : K) * c) := by
  obtain ⟨u, v⟩ := t
  have e : ∀ A B C D X : ModGL F4.tag K, A * B * (C * D) * X * (A * B * (C * D))⁻¹ =
      A * (B * (C * (D * X * D⁻¹) * C⁻¹) * B⁻¹) * A⁻¹ := fun A B C D X => by group
  rw [torusPair_apply, e, root_torus_conjugation _ hβ, root_torus_conjugation _ hβ,
    root_torus_conjugation _ hβ, root_torus_conjugation _ hβ]
  congr 1
  have hpow : ∀ (w : Kˣ) (m : ℤ), (w ^ 2 ^ a) ^ m = w ^ (m * 2 ^ a) := fun w m => by
    rw [← zpow_natCast, ← zpow_mul]
    congr 1
    push_cast
    ring
  have hw : torusWeight a β (u, v) = u ^ (∑ k, F4.tag.cartan (f4i 0) k * β k) *
      (u ^ 2 ^ a) ^ (∑ k, F4.tag.cartan (f4i 3) k * β k) *
      (v ^ (∑ k, F4.tag.cartan (f4i 1) k * β k) *
        (v ^ 2 ^ a) ^ (∑ k, F4.tag.cartan (f4i 2) k * β k)) := by
    rw [torusWeight_apply, hpow, hpow]
    simp only [torusExp0, torusExp1, cartanPair, zpow_add]
  rw [hw]
  simp only [Units.val_mul]
  ring

theorem torusWeight_surjective
    [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    {α : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α) (hαp : 0 < height α) :
    Function.Surjective (torusWeight (K := K) a α) := by
  have hN : ∀ g : Kˣ, g ^ (2 * (2 ^ a : ℤ) ^ 2 - 1) = 1 := fun g => by
    have h1 : g ^ Nat.card Kˣ = 1 := pow_card_eq_one'
    rw [Nat.card_units, hK] at h1
    have e : (2 * (2 ^ a : ℤ) ^ 2 - 1) = ((2 ^ (2 * a + 1) - 1 : ℕ) : ℤ) := by
      rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
        two_pow_two_mul_add_one, add_sub_cancel_right]
    rw [e, zpow_natCast]
    exact h1
  have key : ∀ (E : ℤ), IsCoprime E (2 * (2 ^ a : ℤ) ^ 2 - 1) → ∀ g : Kˣ, ∃ u : Kˣ,
      u ^ E = g := fun E hE g => by
    obtain ⟨x, y, hxy⟩ := hE
    refine ⟨g ^ x, ?_⟩
    rw [← zpow_mul, mul_comm, show E * x = 1 - y * (2 * (2 ^ a : ℤ) ^ 2 - 1) by linarith,
      zpow_sub, zpow_one, zpow_mul, hN, inv_one, mul_one]
  intro g
  rcases f4_torusExp_isCoprime (2 ^ a) hα hαp with h | h
  · obtain ⟨u, hu⟩ := key _ h g
    exact ⟨(u, 1), by rw [torusWeight_fst, hu]⟩
  · obtain ⟨v, hv⟩ := key _ h g
    exact ⟨(1, v), by rw [torusWeight_snd, hv]⟩

theorem torusWeight_ne_one
    [Finite K] (ha : 2 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {β : Fin F4.tag.rank → ℤ} (hβ : IsRoot F4.tag β) (hβp : 0 < height β) :
    torusWeight (K := K) a β ≠ 1 := by
  intro h1
  obtain ⟨g, hg⟩ := exists_orderOf_eq_card_sub_one (K := K)
  have hN : ((orderOf g : ℕ) : ℤ) = 2 * (2 ^ a : ℤ) ^ 2 - 1 := by
    rw [hg, hK, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
      two_pow_two_mul_add_one a, add_sub_cancel_right]
  have h0 : g ^ torusExp0 (2 ^ a) β = 1 := by
    rw [← torusWeight_fst, h1, MonoidHom.one_apply]
  have h1' : g ^ torusExp1 (2 ^ a) β = 1 := by
    rw [← torusWeight_snd, h1, MonoidHom.one_apply]
  rw [← orderOf_dvd_iff_zpow_eq_one, hN] at h0 h1'
  refine f4_torusExp_pair_not_dvd ha hβ hβp hβ hβp 0 0 ⟨?_, ?_⟩
  · simpa [← two_mul] using dvd_mul_of_dvd_right h0 2
  · simpa [← two_mul] using dvd_mul_of_dvd_right h1' 2

theorem torusWeight_form_eq_zero
    [Finite K] [CharP K 2] (ha : 2 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {α β : Fin F4.tag.rank → ℤ} (hα : IsRoot F4.tag α)
    (hαp : 0 < height α) (hβ : IsRoot F4.tag β) (hβp : 0 < height β) (F : K → K → ZMod 2)
    (hF₁ : ∀ c₁ c₂ d, F (c₁ + c₂) d = F c₁ d + F c₂ d)
    (hF₂ : ∀ c d₁ d₂, F c (d₁ + d₂) = F c d₁ + F c d₂)
    (hFT : ∀ (t : Kˣ × Kˣ) c d,
      F ((torusWeight a α t : K) * c) ((torusWeight a β t : K) * d) = F c d) :
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
    Nat.prime_two (n := 2 * a + 1)
    (by omega) hK
  obtain ⟨A, hA, hAuniq⟩ := h2 G
  have hcoef : ∀ (t : Kˣ × Kˣ) (i j : Fin (2 * a + 1)),
      A i j * ((torusWeight a α t : K) ^ 2 ^ (i : ℕ) * (torusWeight a β t : K) ^ 2 ^ (j : ℕ)) =
        A i j := by
    intro t
    have huniq := hAuniq
      (fun i j => A i j * ((torusWeight a α t : K) ^ 2 ^ (i : ℕ) *
        (torusWeight a β t : K) ^ 2 ^ (j : ℕ))) fun x y => by
      have h1 : G x y = G ((torusWeight a α t : K) * x) ((torusWeight a β t : K) * y) := by
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
    have key : ∀ t : Kˣ × Kˣ, ((torusWeight a α t ^ 2 ^ (i : ℕ) *
        torusWeight a β t ^ 2 ^ (j : ℕ) : Kˣ) : K) = 1 := fun t => by
      rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val]
      exact (mul_eq_left₀ hne).1 (hcoef t i j)
    obtain ⟨g, hg⟩ := exists_orderOf_eq_card_sub_one (K := K)
    have hN : ((orderOf g : ℕ) : ℤ) = 2 * (2 ^ a : ℤ) ^ 2 - 1 := by
      rw [hg, hK, Nat.cast_sub (Nat.one_le_two_pow), Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one,
        two_pow_two_mul_add_one a, add_sub_cancel_right]
    have hdvd : ∀ (e e' : ℤ), ((g ^ e) ^ 2 ^ (i : ℕ) * (g ^ e') ^ 2 ^ (j : ℕ) : Kˣ) = 1 →
        (2 * (2 ^ a : ℤ) ^ 2 - 1) ∣ 2 ^ (i : ℕ) * e + 2 ^ (j : ℕ) * e' := by
      intro e e' he
      rw [← hN, orderOf_dvd_iff_zpow_eq_one, zpow_add, mul_comm ((2 : ℤ) ^ (i : ℕ)),
        mul_comm ((2 : ℤ) ^ (j : ℕ)), zpow_mul, zpow_mul]
      exact_mod_cast he
    refine f4_torusExp_pair_not_dvd ha hα hαp hβ hβp i j ⟨hdvd _ _ ?_, hdvd _ _ ?_⟩
    · have h := key (g, 1)
      rw [torusWeight_fst, torusWeight_fst] at h
      exact Units.val_eq_one.1 h
    · have h := key (1, g)
      rw [torusWeight_snd, torusWeight_snd] at h
      exact Units.val_eq_one.1 h
  intro c d
  have h0 : G c d = 0 := by
    rw [hA]
    simp [hA0]
  exact hι (by rw [map_zero, ← hG]; exact h0)

end CFSG.LieType.Ree.LargeReeCover
