module

public import CFSG.CharacterTheory.Semidihedral.Local.FourGroupCyclingOddControlSupport

public section

namespace CFSG.Wreathed

variable {G : Type*} [Group G]

theorem le_normalizer_of_conj_mem {H J : Subgroup G}
    (h : ∀ g ∈ H, ∀ x ∈ J, g * x * g⁻¹ ∈ J) : H ≤ Subgroup.normalizer (J : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (H.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem conj_mem_sup {J₁ J₂ : Subgroup G} {g : G} (h₁ : ∀ x ∈ J₁, g * x * g⁻¹ ∈ J₁ ⊔ J₂)
    (h₂ : ∀ x ∈ J₂, g * x * g⁻¹ ∈ J₁ ⊔ J₂) {x : G} (hx : x ∈ J₁ ⊔ J₂) :
    g * x * g⁻¹ ∈ J₁ ⊔ J₂ := by
  have hle : J₁ ⊔ J₂ ≤ (J₁ ⊔ J₂).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun y hy => by simpa using h₁ y hy) (fun y hy => by simpa using h₂ y hy)
  simpa using hle hx

theorem subgroupOf_le_pPrimeCore_of_sup_eq [Finite G] (p : ℕ) [Fact p.Prime]
    {H K M N₀ : Subgroup G} (hM : M ≤ H) (hN₀ : N₀ ≤ (pPrimeCore p H).map H.subtype)
    (hsup : N₀ ⊔ M = H) (hMK : M ≤ Subgroup.normalizer (K : Set G))
    (hK : Nat.Coprime p (Nat.card K)) : K.subgroupOf H ≤ pPrimeCore p H := by
  have hN₀H : N₀ ≤ H := hN₀.trans (Subgroup.map_subtype_le _)
  have hN₀ker : N₀.subgroupOf H ≤ pPrimeCore p H := by
    intro z hz
    obtain ⟨w, hw, hwz⟩ := hN₀ (Subgroup.mem_subgroupOf.mp hz)
    rwa [← Subtype.ext hwz]
  have hN₀bar : (N₀.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore p H)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    exact hN₀ker
  have hMtop : (M.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore p H)) = ⊤ := by
    have h1 : (N₀ ⊔ M).subgroupOf H = ⊤ := by
      rw [hsup]
      exact Subgroup.subgroupOf_self H
    rw [Subgroup.subgroupOf_sup hN₀H hM] at h1
    have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (pPrimeCore p H))) h1
    rwa [Subgroup.map_sup, hN₀bar, bot_sup_eq,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  have hnorm : ((K.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore p H))).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hMtop]
    refine le_trans (Subgroup.map_mono ?_) (Subgroup.le_normalizer_map _)
    intro m hm
    have hmK := hMK (Subgroup.mem_subgroupOf.mp hm)
    rw [Subgroup.mem_normalizer_iff] at hmK ⊢
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact hmK z
  have hcop : Nat.Coprime p
      (Nat.card ((K.subgroupOf H).map (QuotientGroup.mk' (pPrimeCore p H)))) := by
    refine hK.coprime_dvd_right ((Subgroup.card_map_dvd _ _).trans ?_)
    rw [Semidihedral.Local.card_subgroupOf_eq]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hle : _ ≤ pPrimeCore p (H ⧸ pPrimeCore p H) := le_sSup ⟨hnorm, hcop⟩
  rw [Semidihedral.Local.pPrimeCore_quotient_self_eq_bot, le_bot_iff, Subgroup.map_eq_bot_iff,
    QuotientGroup.ker_mk'] at hle
  exact hle

theorem subgroupMap_mk_pPrimeCore_injective {E : Type*} [Group E] [Finite E] (p : ℕ)
    [Fact p.Prime] (P : Subgroup E) (hP : IsPGroup p P) :
    Function.Injective ((QuotientGroup.mk' (pPrimeCore p E)).subgroupMap P) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  have hz' : QuotientGroup.mk' (pPrimeCore p E) (z : E) = 1 := congrArg Subtype.val hz
  have hz1 : (z : E) ∈ pPrimeCore p E := (QuotientGroup.eq_one_iff _).mp hz'
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hP
  have hcop : Nat.Coprime (Nat.card P) (Nat.card (pPrimeCore p E)) := by
    rw [hk]
    exact Nat.Coprime.pow_left k pPrimeCore_coprime_card
  exact Subtype.ext (Subgroup.disjoint_def.mp (Subgroup.disjoint_of_coprime_natCard hcop) z.2 hz1)

noncomputable def mapMkPPrimeCoreEquiv {E : Type*} [Group E] [Finite E] (p : ℕ) [Fact p.Prime]
    (P : Subgroup E) (hP : IsPGroup p P) : P ≃* P.map (QuotientGroup.mk' (pPrimeCore p E)) :=
  MulEquiv.ofBijective _ ⟨subgroupMap_mk_pPrimeCore_injective p P hP,
    (QuotientGroup.mk' (pPrimeCore p E)).subgroupMap_surjective P⟩

theorem le_centralizer_of_normal_of_coprime {Q : Type*} [Group Q] {V Y : Subgroup Q} [V.Normal]
    (hVY : V ≤ Subgroup.normalizer (Y : Set Q)) (hcop : Nat.Coprime (Nat.card Y) (Nat.card V)) :
    Y ≤ Subgroup.centralizer (V : Set Q) := by
  intro w hw
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 : v * w * v⁻¹ * w⁻¹ ∈ Y :=
    Y.mul_mem ((Subgroup.mem_normalizer_iff.mp (hVY hv) w).mp hw) (Y.inv_mem hw)
  have h2 : v * w * v⁻¹ * w⁻¹ ∈ V := by
    have h := V.mul_mem hv ((inferInstance : V.Normal).conj_mem _ (V.inv_mem hv) w)
    simpa only [mul_assoc] using h
  exact Semidihedral.Local.mul_comm_of_mul_mul_inv_mul_inv_eq_one
    (Subgroup.disjoint_def.mp (Subgroup.disjoint_of_coprime_natCard hcop) h1 h2)

theorem commutator_mem_of_cycling (T : Subgroup G) [IsKleinFour T] {A K : Subgroup G} {x g : G}
    (hxT : x ∈ T) (hx1 : x ≠ 1) (hTK : T ≤ Subgroup.normalizer (K : Set G))
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hgK : g ∈ Subgroup.normalizer (K : Set G))
    (hgT : g ∈ Subgroup.normalizer (T : Set G)) (hg : g * x * g⁻¹ ≠ x)
    (hx : ∀ a ∈ A, x * a * x⁻¹ * a⁻¹ ∈ K) : ∀ v ∈ T, ∀ a ∈ A, v * a * v⁻¹ * a⁻¹ ∈ K := by
  have huT : g * x * g⁻¹ ∈ T := (Subgroup.mem_normalizer_iff.mp hgT x).mp hxT
  have hu1 : g * x * g⁻¹ ≠ 1 := fun h => hx1 (by
    have h' : x = g⁻¹ * (g * x * g⁻¹) * g := by group
    rw [h', h]
    group)
  have hu : ∀ a ∈ A, g * x * g⁻¹ * a * (g * x * g⁻¹)⁻¹ * a⁻¹ ∈ K := fun a ha =>
    Semidihedral.Local.conj_commutator_mem hgA hgK hx ha
  intro v hv a ha
  rcases Semidihedral.Local.kleinFour_mem_cases T hxT huT hx1 hu1 (Ne.symm hg) hv with
    rfl | rfl | rfl | rfl
  · exact Semidihedral.Local.mul_commutator_mem (hTK hxT) hx hu ha
  · exact hx a ha
  · exact hu a ha
  · simp

theorem isPGroup_of_mulEquiv_prod {Q : Type*} [Group Q] (a b : ℕ)
    (e : Q ≃* Multiplicative (ZMod (2 ^ a)) × Multiplicative (ZMod (2 ^ b))) :
    IsPGroup 2 Q := by
  refine IsPGroup.of_card (n := a + b) ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, pow_add,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (2 ^ a)) ≃ _),
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (2 ^ b)) ≃ _),
    Nat.card_zmod, Nat.card_zmod]

theorem mem_of_sq_eq_one_of_card_four {Q : Type*} [Group Q] [Finite Q] (a b : ℕ)
    (e : Q ≃* Multiplicative (ZMod (2 ^ a)) × Multiplicative (ZMod (2 ^ b))) (P : Subgroup Q)
    (hP : Nat.card P = 4) (hP2 : ∀ r ∈ P, r ^ 2 = 1) {q : Q} (hq : q ^ 2 = 1) : q ∈ P := by
  classical
  let _ : Fintype Q := Fintype.ofFinite Q
  have h1 : (Finset.univ.filter fun u : Multiplicative (ZMod (2 ^ a)) => u ^ 2 = 1).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have h2 : (Finset.univ.filter fun u : Multiplicative (ZMod (2 ^ b)) => u ^ 2 = 1).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (by norm_num)
  have hZ : (Finset.univ.filter fun z : Multiplicative (ZMod (2 ^ a)) ×
      Multiplicative (ZMod (2 ^ b)) => z ^ 2 = 1).card ≤ 4 := by
    calc _ ≤ ((Finset.univ.filter fun u : Multiplicative (ZMod (2 ^ a)) => u ^ 2 = 1) ×ˢ
          (Finset.univ.filter fun u : Multiplicative (ZMod (2 ^ b)) => u ^ 2 = 1)).card := by
          apply Finset.card_le_card
          intro z hz
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product] at hz ⊢
          rw [Prod.ext_iff] at hz
          exact ⟨by simpa using hz.1, by simpa using hz.2⟩
      _ = _ * _ := Finset.card_product _ _
      _ ≤ 2 * 2 := Nat.mul_le_mul h1 h2
  have hQ : (Finset.univ.filter fun r : Q => r ^ 2 = 1).card ≤ 4 := by
    refine le_trans (Finset.card_le_card_of_injOn e ?_ e.injective.injOn) hZ
    intro r hr
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hr ⊢
    rw [← map_pow, hr, map_one]
  have hsub : (Finset.univ.filter fun r : Q => r ∈ P) ⊆
      Finset.univ.filter fun r : Q => r ^ 2 = 1 := by
    intro r hr
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr ⊢
    exact hP2 r hr
  have hcardP : (Finset.univ.filter fun r : Q => r ∈ P).card = 4 := by
    rw [← hP, Nat.card_eq_fintype_card, Fintype.card_subtype]
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcardP]; exact hQ)
  have hqmem : q ∈ Finset.univ.filter fun r : Q => r ^ 2 = 1 := by simp [hq]
  rw [← heq] at hqmem
  simpa using hqmem

theorem mem_of_pow_eq_one_of_isPGroup_quotient {Q : Type*} [Group Q] {p : ℕ} (N : Subgroup Q)
    [N.Normal] (hN : IsPGroup p (Q ⧸ N)) {c : Q} {m : ℕ} (hm : Nat.Coprime p m)
    (hc : c ^ m = 1) : c ∈ N := by
  obtain ⟨k, hk⟩ := hN (c : Q ⧸ N)
  have h1 : orderOf (c : Q ⧸ N) ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  have h2 : orderOf (c : Q ⧸ N) ∣ m :=
    orderOf_dvd_of_pow_eq_one (by rw [← QuotientGroup.mk_pow, hc, QuotientGroup.mk_one])
  have h3 : orderOf (c : Q ⧸ N) = 1 := Nat.eq_one_of_dvd_coprimes (hm.pow_left k) h1 h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

end CFSG.Wreathed
