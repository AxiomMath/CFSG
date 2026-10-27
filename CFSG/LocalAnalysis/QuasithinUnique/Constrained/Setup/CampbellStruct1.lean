module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellSeed
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic

public section

namespace CFSG.QuasithinUnique.Setup.Campbell

open Subgroup CFSG CFSG.Quasithin CFSG.Quasithin.BlueprintB2 CFSG.SL2MinimalFaithful
open scoped LinearAlgebra.Projectivization commutatorElement

section General

variable {G : Type*} [Group G]

theorem exists_odd_two_decomp [Finite G] (n : G) :
    ∃ y z : G, y ∈ Subgroup.zpowers n ∧ z ∈ Subgroup.zpowers n ∧ n = y * z ∧
      (∃ m : ℕ, Odd m ∧ y ^ m = 1) ∧ ∃ k : ℕ, z ^ 2 ^ k = 1 := by
  have hn : IsOfFinOrder n := isOfFinOrder_of_finite n
  have hpos : 0 < orderOf n := hn.orderOf_pos
  obtain ⟨k, m, hm, ho⟩ := Nat.exists_eq_two_pow_mul_odd hpos.ne'
  have hcop : IsCoprime (((2 ^ k : ℕ)) : ℤ) (m : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm))
  obtain ⟨u, v, huv⟩ := hcop
  have hpow : n ^ (orderOf n) = 1 := pow_orderOf_eq_one n
  have hy : ((n ^ 2 ^ k) ^ u) ^ m = 1 := by
    have h1 : (n ^ 2 ^ k) ^ m = 1 := by rw [← pow_mul, ← ho, hpow]
    calc ((n ^ 2 ^ k) ^ u) ^ m = ((n ^ 2 ^ k) ^ m) ^ u := by
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      _ = 1 := by rw [h1, one_zpow]
  have hz : ((n ^ m) ^ v) ^ 2 ^ k = 1 := by
    have h1 : (n ^ m) ^ 2 ^ k = 1 := by rw [← pow_mul, mul_comm, ← ho, hpow]
    calc ((n ^ m) ^ v) ^ 2 ^ k = ((n ^ m) ^ 2 ^ k) ^ v := by
          rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
      _ = 1 := by rw [h1, one_zpow]
  refine ⟨(n ^ 2 ^ k) ^ u, (n ^ m) ^ v,
    Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers n) _) _,
    Subgroup.zpow_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers n) _) _, ?_, ⟨m, hm, hy⟩, ⟨k, hz⟩⟩
  calc n = n ^ (u * ((2 ^ k : ℕ) : ℤ) + v * (m : ℤ)) := by rw [huv, zpow_one]
    _ = n ^ (u * ((2 ^ k : ℕ) : ℤ)) * n ^ (v * (m : ℤ)) := zpow_add _ _ _
    _ = (n ^ 2 ^ k) ^ u * (n ^ m) ^ v := by
      rw [mul_comm u, mul_comm v, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]

end General

section VDefs

variable {G : Type*} [Group G]

@[expose] def Kodd (G : Type*) [Group G] : Subgroup G := pPrimeGen 2 (⊤ : Subgroup G)

@[expose] def Vmod (G : Type*) [Group G] : Subgroup G := ⁅Ecore G, Kodd G⁆

instance Kodd_normal : (Kodd G).Normal := pPrimeGen_top_normal

instance Vmod_normal : (Vmod G).Normal := by
  unfold Vmod; infer_instance

theorem Vmod_le_Ecore : Vmod G ≤ Ecore G := Subgroup.commutator_le_left _ _

theorem Kodd_closure [Finite G] :
    Subgroup.closure {x : G | x ∈ Kodd G ∧ ¬ 2 ∣ orderOf x} = Kodd G := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  · unfold Kodd pPrimeGen
    refine Subgroup.closure_mono fun x hx => ⟨?_, ?_⟩
    · exact Subgroup.subset_closure hx
    · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hx.2.symm

theorem Vmod_commutator [Finite G] : ⁅Vmod G, Kodd G⁆ = Vmod G := by
  have h0 : IsPGroup 2 (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  have := (prime_residual_commutator_through_normal_layer (p := 2) (E := (⊥ : Subgroup G))
    (Q := (⊥ : Subgroup G)) (K := Kodd G) le_rfl h0 Kodd_closure (by simp)).2 (Ecore G)
    ((CFSG.pCore_isPGroup (G := G) (p := 2)).to_le Ecore_le_core)
  exact this

instance Vmod_commGroup : CommGroup (Vmod G) :=
  { (inferInstance : Group (Vmod G)) with
    mul_comm := fun a b => Subtype.ext (Ecore_commute (Vmod_le_Ecore a.2) (Vmod_le_Ecore b.2)) }

theorem Vmod_sq {x : G} (hx : x ∈ Vmod G) : x ^ 2 = 1 := Ecore_sq (Vmod_le_Ecore hx)

theorem exists_descend {H M : Type*} [Group H] [Group M] (ρ : G →* H)
    (hρ : Function.Surjective ρ) (f : G →* M) (hker : ρ.ker ≤ f.ker) :
    ∃ F : H →* M, ∀ g, F (ρ g) = f g :=
  ⟨MonoidHom.liftOfRightInverse ρ (Function.surjInv hρ) (Function.rightInverse_surjInv hρ)
      ⟨f, hker⟩, fun g => MonoidHom.liftOfRightInverse_comp_apply ρ _ _ ⟨f, hker⟩ g⟩

end VDefs


section Struct

variable {G : Type*} [Group G] {k : Type*} [Field k] {S : Sylow 2 G}
  {ρ : G →* Matrix.SpecialLinearGroup (Fin 2) k} {ψ : Ecore G →* Multiplicative (Fin 2 → k)}

namespace IsNatBase

theorem ψ_eq_one_iff (h : IsNatBase S ρ (Ecore G) ψ) {e : Ecore G} :
    ψ e = 1 ↔ (e : G) ∈ Subgroup.center G := by
  have : e ∈ ψ.ker ↔ ψ e = 1 := MonoidHom.mem_ker
  rw [← this, h.ψ_ker, Subgroup.mem_subgroupOf]
  simp [e.2]

theorem commutator_ker_mem_center (h : IsNatBase S ρ (Ecore G) ψ) {y : G} (hy : y ∈ ρ.ker)
    (e : Ecore G) : y * e * y⁻¹ * e⁻¹ ∈ Subgroup.center G := by
  have hρy : ρ y = 1 := hy
  set e' : Ecore G := ⟨y * e * y⁻¹, (inferInstance : (Ecore G).Normal).conj_mem e e.2 y⟩ with he'
  have h1 : ψ e' = ψ e := by
    apply Multiplicative.toAdd.injective
    have := h.ψ_equiv y e e' rfl
    rw [this, hρy]
    simp
  have h2 : ψ (e' * e⁻¹) = 1 := by rw [map_mul, map_inv, h1, mul_inv_cancel]
  have := (h.ψ_eq_one_iff).mp h2
  simpa using this

theorem ker_le_centralizer_Ecore [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ) :
    ρ.ker ≤ Subgroup.centralizer (Ecore G : Set G) := by
  classical
  intro n hn
  obtain ⟨y, z, hyn, hzn, hnyz, ⟨m, hm, hym⟩, ⟨k', hzk⟩⟩ := exists_odd_two_decomp n
  have hyN : y ∈ ρ.ker := Subgroup.zpowers_le.mpr hn hyn
  have hzN : z ∈ ρ.ker := Subgroup.zpowers_le.mpr hn hzn
  have hP : IsPGroup 2 (Subgroup.zpowers z) := by
    rintro ⟨g, hg⟩
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    refine ⟨k', Subtype.ext ?_⟩
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hzk, one_zpow]
  have hzQ : z ∈ CFSG.pCore 2 G := h.ker_inf_le_core hP ⟨hzN, Subgroup.mem_zpowers z⟩
  have hzE : z ∈ Subgroup.centralizer (Ecore G : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun e he => (Ecore_commute_core hzQ he).symm
  have hcop : Nat.Coprime (orderOf y) (Nat.card (Ecore G ⊓ Subgroup.center G : Subgroup G)) := by
    have hp : IsPGroup 2 (Ecore G ⊓ Subgroup.center G : Subgroup G) :=
      (CFSG.pCore_isPGroup (G := G) (p := 2)).to_le (inf_le_left.trans Ecore_le_core)
    obtain ⟨b, hb⟩ := (IsPGroup.iff_card).mp hp
    rw [hb]
    exact Nat.Coprime.pow_right _
      (Nat.coprime_two_right.mpr (hm.of_dvd_nat (orderOf_dvd_of_pow_eq_one hym)))
  have hyE : y ∈ Subgroup.centralizer (Ecore G : Set G) := by
    have key := coprime_conj_mem (G := G) (Q := Ecore G) (U := Ecore G ⊓ Subgroup.center G)
      (W := ⊥) (x := y) inf_le_left bot_le
      (fun q _ w hw => by rw [Subgroup.mem_bot] at hw; rw [hw]; simp)
      (fun u hu => by
        have := Subgroup.mem_center_iff.mp hu.2 y
        rw [Subgroup.mem_bot]
        calc y * u * y⁻¹ * u⁻¹ = (u * y) * y⁻¹ * u⁻¹ := by rw [this]
          _ = 1 := by group)
      (fun q hq => by
        have h1 := h.commutator_ker_mem_center hyN ⟨q, hq⟩
        have h2 : y * q * y⁻¹ ∈ Ecore G := (inferInstance : (Ecore G).Normal).conj_mem q hq y
        exact Subgroup.mem_inf.mpr ⟨(Ecore G).mul_mem h2 ((Ecore G).inv_mem hq), h1⟩)
      hcop
    refine Subgroup.mem_centralizer_iff.mpr fun e he => ?_
    have h1 := key e he
    rw [Subgroup.mem_bot] at h1
    have h2 : y * e * y⁻¹ = e := by
      calc y * e * y⁻¹ = (y * e * y⁻¹ * e⁻¹) * e := by group
        _ = e := by rw [h1]; simp
    have h3 : y * e = e * y := by
      calc y * e = (y * e * y⁻¹) * y := by group
        _ = e * y := by rw [h2]
    exact h3.symm
  rw [hnyz]
  exact mul_mem hyE hzE

theorem ψ_Vmod_surj [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ)
    (w : Multiplicative (Fin 2 → k)) : ∃ v : Ecore G, (v : G) ∈ Vmod G ∧ ψ v = w := by
  classical
  have := h.charP_two
  obtain ⟨n, hn, hk⟩ := h.card_k
  have h3 : 3 ∣ Nat.card (Matrix.SpecialLinearGroup (Fin 2) k) := by
    rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hk]
    refine Dvd.dvd.mul_left ?_ _
    have h4 : (2 ^ n) ^ 2 = 4 ^ n := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
    rw [h4]
    simpa using Nat.sub_one_dvd_pow_sub_one 4 n
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs3⟩ := exists_prime_orderOf_dvd_card' (G := Matrix.SpecialLinearGroup (Fin 2) k) 3 h3
  obtain ⟨g, hg⟩ := h.surj s
  obtain ⟨a, ha⟩ := exists_pow_mem_pPrimeGen (p := 2) (X := (⊤ : Subgroup G)) (x := g)
    (Subgroup.mem_top g)
  set y : G := g ^ 2 ^ a with hy
  have hyK : y ∈ Kodd G := ha
  have hρy : ρ y = s ^ 2 ^ a := by rw [hy, map_pow, hg]
  have hord : orderOf (ρ y) = 3 := by
    rw [hρy, Nat.Coprime.orderOf_pow, hs3]
    rw [hs3]
    exact Nat.Coprime.pow_right a (by decide)
  set s' := ρ y with hs'
  have hfix : ∀ v : Fin 2 → k, s' • v = v → v = 0 := by
    intro v hv
    by_contra hv0
    have hmem := mem_rootGrp_mk_of_smul_eq hv0 hv
    have hsq := mul_self_eq_one_of_mem_rootGrp hmem
    have : orderOf s' ∣ 2 := orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact hsq)
    rw [hord] at this
    omega
  let f : (Fin 2 → k) →+ (Fin 2 → k) :=
    { toFun := fun v => s' • v - v
      map_zero' := by simp
      map_add' := fun a b => by simp [smul_add]; abel }
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_zero]
    intro v hv
    exact hfix v (sub_eq_zero.mp hv)
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd w)
  obtain ⟨e, he⟩ := h.ψ_surj (Multiplicative.ofAdd u)
  have hye : y * (e : G) * y⁻¹ ∈ Ecore G := (inferInstance : (Ecore G).Normal).conj_mem e e.2 y
  have hc : y * (e : G) * y⁻¹ * (e : G)⁻¹ ∈ Vmod G := by
    have : ⁅y, (e : G)⁆ ∈ ⁅Kodd G, Ecore G⁆ := Subgroup.commutator_mem_commutator hyK e.2
    rw [Subgroup.commutator_comm] at this
    unfold Vmod
    simpa [commutatorElement_def] using this
  refine ⟨⟨y * (e : G) * y⁻¹ * (e : G)⁻¹, (Ecore G).mul_mem hye ((Ecore G).inv_mem e.2)⟩, hc, ?_⟩
  have hψ1 := h.ψ_equiv y e ⟨y * (e : G) * y⁻¹, hye⟩ rfl
  have hmul : (⟨y * (e : G) * y⁻¹ * (e : G)⁻¹, (Ecore G).mul_mem hye ((Ecore G).inv_mem e.2)⟩ :
      Ecore G) = ⟨y * (e : G) * y⁻¹, hye⟩ * e⁻¹ := rfl
  rw [hmul, map_mul, map_inv, he]
  apply Multiplicative.toAdd.injective
  rw [toAdd_mul, toAdd_inv, hψ1, he, toAdd_ofAdd, ← hu]
  show _ = s' • u - u
  rw [sub_eq_add_neg, Matrix.SpecialLinearGroup.smul_def]
  rfl

theorem Ecore_eq_Vmod_sup [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ) :
    Ecore G = Vmod G ⊔ (Ecore G ⊓ Subgroup.center G) := by
  apply le_antisymm
  · intro e he
    obtain ⟨v, hv, hψ⟩ := h.ψ_Vmod_surj (ψ ⟨e, he⟩)
    have hker : ψ (v⁻¹ * ⟨e, he⟩) = 1 := by rw [map_mul, map_inv, hψ, inv_mul_cancel]
    have hc : ((v⁻¹ * ⟨e, he⟩ : Ecore G) : G) ∈ Subgroup.center G := (h.ψ_eq_one_iff).mp hker
    have h1 : e = (v : G) * ((v : G)⁻¹ * e) := by group
    rw [h1]
    exact mul_mem (Subgroup.mem_sup_left hv)
      (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr
        ⟨(Ecore G).mul_mem ((Ecore G).inv_mem v.2) he, hc⟩))
  · exact sup_le Vmod_le_Ecore inf_le_left

theorem exists_natPlane [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ) :
    ∃ act : Matrix.SpecialLinearGroup (Fin 2) k →* MulAut ↥(Vmod G),
      (∀ (g : G) (v : Vmod G), ((act (ρ g) v : Vmod G) : G) = g * v * g⁻¹) ∧
      IsNatPlane act (ψ.comp (Subgroup.inclusion Vmod_le_Ecore)) ∧
      commSub act Set.univ ⊤ = ⊤ := by
  classical
  have hker : ρ.ker ≤ (MulAut.conjNormal (H := Vmod G)).ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    apply MulEquiv.ext
    intro v
    show MulAut.conjNormal n v = v
    apply Subtype.ext
    rw [MulAut.conjNormal_apply]
    have := Subgroup.mem_centralizer_iff.mp (h.ker_le_centralizer_Ecore hn) (v : G)
      (Vmod_le_Ecore v.2)
    calc n * (v : G) * n⁻¹ = (v : G) * n * n⁻¹ := by rw [← this]
      _ = v := by group
  obtain ⟨act, hact⟩ := exists_descend ρ h.surj (MulAut.conjNormal (H := Vmod G)) hker
  have hact' : ∀ (g : G) (v : Vmod G), ((act (ρ g) v : Vmod G) : G) = g * v * g⁻¹ := by
    intro g v
    rw [hact]; rfl
  refine ⟨act, hact', ⟨?_, ?_, ?_, ?_⟩, ?_⟩
  · intro e
    exact Subtype.ext (by simpa [pow_two] using Vmod_sq e.2)
  · intro w
    obtain ⟨v, hv, hψ⟩ := h.ψ_Vmod_surj w
    exact ⟨⟨v, hv⟩, hψ⟩
  · intro g e
    obtain ⟨g₀, rfl⟩ := h.surj g
    have h1 := h.ψ_equiv g₀ (Subgroup.inclusion Vmod_le_Ecore e)
      (Subgroup.inclusion Vmod_le_Ecore (act (ρ g₀) e)) (by
        show ((act (ρ g₀) e : Vmod G) : G) = g₀ * (e : G) * g₀⁻¹
        exact hact' g₀ e)
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    exact h1
  · intro g e he
    obtain ⟨g₀, rfl⟩ := h.surj g
    have h1 : ψ (Subgroup.inclusion Vmod_le_Ecore e) = 1 := he
    have hc := (h.ψ_eq_one_iff).mp h1
    apply Subtype.ext
    rw [hact']
    have h2 : g₀ * (e : G) = (e : G) * g₀ := Subgroup.mem_center_iff.mp hc g₀
    calc g₀ * (e : G) * g₀⁻¹ = (e : G) * g₀ * g₀⁻¹ := by rw [h2]
      _ = e := by group
  · rw [eq_top_iff]
    intro v _
    have hv : (v : G) ∈ (⁅Vmod G, Kodd G⁆ : Subgroup G) := by rw [Vmod_commutator]; exact v.2
    have key : ∀ x ∈ (⁅Vmod G, Kodd G⁆ : Subgroup G),
        ∃ hx : x ∈ Vmod G, (⟨x, hx⟩ : Vmod G) ∈ commSub act Set.univ ⊤ := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨a, ha, b, hb, rfl⟩ := hx
        have hxV : ⁅a, b⁆ ∈ Vmod G := by
          have h1 : b * a⁻¹ * b⁻¹ ∈ Vmod G :=
            (inferInstance : (Vmod G).Normal).conj_mem a⁻¹ ((Vmod G).inv_mem ha) b
          have := (Vmod G).mul_mem ha h1
          simpa [commutatorElement_def, mul_assoc] using this
        refine ⟨hxV, ?_⟩
        have hmem : act (ρ b) ⟨a, ha⟩ * (⟨a, ha⟩ : Vmod G)⁻¹ ∈ commSub act Set.univ ⊤ :=
          Subgroup.subset_closure ⟨ρ b, Set.mem_univ _, ⟨a, ha⟩, Subgroup.mem_top _, rfl⟩
        have heq : (⟨⁅a, b⁆, hxV⟩ : Vmod G) = (act (ρ b) ⟨a, ha⟩ * (⟨a, ha⟩ : Vmod G)⁻¹)⁻¹ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv, hact', commutatorElement_def]
          group
        rw [heq]
        exact inv_mem hmem
      | one => exact ⟨one_mem _, one_mem _⟩
      | mul x y hx hy ihx ihy =>
        obtain ⟨hxV, hxW⟩ := ihx
        obtain ⟨hyV, hyW⟩ := ihy
        exact ⟨mul_mem hxV hyV, mul_mem hxW hyW⟩
      | inv x hx ih =>
        obtain ⟨hxV, hxW⟩ := ih
        exact ⟨inv_mem hxV, inv_mem hxW⟩
    obtain ⟨hvV, hvW⟩ := key (v : G) hv
    exact hvW

theorem natural_module_facts [Finite G] [Finite k] (h : IsNatBase S ρ (Ecore G) ψ)
    {ℓ : ℙ k (Fin 2 → k)} (hℓ : (S : Subgroup G).map ρ = rootGrp ℓ) :
    (∀ s ∈ (S : Subgroup G), s ∉ CFSG.pCore 2 G → ∀ v : Ecore G, (v : G) ∈ Vmod G →
      (s * v * s⁻¹ = v ↔ Multiplicative.toAdd (ψ v) ∈ ℓ.submodule)) ∧
    ⁅(S : Subgroup G), Vmod G⁆ = Vmod G ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) ∧
    (Vmod G ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G)).relIndex (Vmod G) = Nat.card k ∧
    (∀ v : Ecore G, (v : G) ∈ Vmod G → Multiplicative.toAdd (ψ v) ∉ ℓ.submodule →
      ∀ s ∈ (S : Subgroup G), s * v * s⁻¹ = v → s ∈ CFSG.pCore 2 G) := by
  classical
  obtain ⟨act, hact, hnat, hEL⟩ := h.exists_natPlane
  obtain ⟨n, hn, hk⟩ := h.card_k
  have hmain := (saturated_natural_plane_root_fixed_space hn hk hnat hEL).2 ℓ
  obtain ⟨hfix, hcomm, -, hst, -, hstab⟩ := hmain
  have hsρ : ∀ s ∈ (S : Subgroup G), ρ s ∈ rootGrp ℓ := fun s hs => by
    rw [← hℓ]; exact ⟨s, hs, rfl⟩
  have hρne : ∀ s ∈ (S : Subgroup G), s ∉ CFSG.pCore 2 G → ρ s ≠ 1 := by
    intro s hs hsQ h1
    apply hsQ
    have hx : s ∈ (S : Subgroup G) ⊓ ρ.ker := ⟨hs, h1⟩
    rwa [h.sylow_inf_ker] at hx
  have hmemfix : ∀ v : Vmod G, v ∈ fixedSub act (rootGrp ℓ : Set _) ↔
      ∀ s ∈ (S : Subgroup G), s * (v : G) * s⁻¹ = v := by
    intro v
    constructor
    · intro hv s hs
      have := hv (ρ s) (hsρ s hs)
      have h2 := congrArg Subtype.val this
      rw [hact] at h2
      exact h2
    · intro hv t ht
      rw [← hℓ] at ht
      obtain ⟨s, hs, rfl⟩ := ht
      exact Subtype.ext (by rw [hact]; exact hv s hs)
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro s hs hsQ v hv
    have ht1 := hρne s hs hsQ
    have ht := hsρ s hs
    have hfs := (hst (ρ s) ht ht1).1
    have h1 : (s * (v : G) * s⁻¹ = v) ↔
        (⟨v, hv⟩ : Vmod G) ∈ fixedSub act ({ρ s} : Set _) := by
      constructor
      · intro hs' a ha
        rw [Set.mem_singleton_iff] at ha
        rw [ha]
        exact Subtype.ext (by rw [hact]; exact hs')
      · intro hv'
        have := congrArg Subtype.val (hv' (ρ s) (Set.mem_singleton _))
        rw [hact] at this
        exact this
    rw [h1, hfs, hfix]
    rfl
  ·
    have hcf : commSub act (rootGrp ℓ : Set _) ⊤ = fixedSub act (rootGrp ℓ : Set _) :=
      (hfix.trans hcomm).symm
    have h1 : (⁅(S : Subgroup G), Vmod G⁆ : Subgroup G) =
        (commSub act (rootGrp ℓ : Set _) ⊤).map (Vmod G).subtype := by
      rw [Subgroup.commutator_def, commSub, MonoidHom.map_closure]
      congr 1
      ext g
      constructor
      · rintro ⟨s, hs, v, hv, rfl⟩
        refine ⟨act (ρ s) ⟨v, hv⟩ * (⟨v, hv⟩ : Vmod G)⁻¹, ⟨ρ s, hsρ s hs, ⟨v, hv⟩,
          Subgroup.mem_top _, rfl⟩, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hact,
          commutatorElement_def]
      · rintro ⟨x, ⟨a, ha, e, -, rfl⟩, rfl⟩
        rw [← hℓ] at ha
        obtain ⟨s, hs, rfl⟩ := ha
        refine ⟨s, hs, e, e.2, ?_⟩
        simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hact,
          commutatorElement_def]
    have h2 : (fixedSub act (rootGrp ℓ : Set _)).map (Vmod G).subtype =
        Vmod G ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
      ext x
      constructor
      · rintro ⟨e, he, rfl⟩
        refine ⟨e.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
        have := (hmemfix e).mp he g hg
        calc g * (e : G) = (g * e * g⁻¹) * g := by group
          _ = (e : G) * g := by rw [this]
      · rintro ⟨hxV, hxc⟩
        refine ⟨⟨x, hxV⟩, (hmemfix ⟨x, hxV⟩).mpr fun g hg => ?_, rfl⟩
        have := Subgroup.mem_centralizer_iff.mp hxc g hg
        show g * x * g⁻¹ = x
        calc g * x * g⁻¹ = (x * g) * g⁻¹ := by rw [this]
          _ = x := by group
    rw [h1, hcf, h2]
  ·
    obtain ⟨t, ht, ht1⟩ := exists_ne_one_mem_rootGrp ℓ
    have hidx := (hst t ht ht1).2.1
    have hsub : (Vmod G ⊓ Subgroup.centralizer ((S : Subgroup G) : Set G)).subgroupOf (Vmod G) =
        fixedSub act (rootGrp ℓ : Set _) := by
      ext e
      rw [Subgroup.mem_subgroupOf, hmemfix e]
      constructor
      · rintro ⟨-, hc⟩ s hs
        have := Subgroup.mem_centralizer_iff.mp hc s hs
        calc s * (e : G) * s⁻¹ = ((e : G) * s) * s⁻¹ := by rw [this]
          _ = e := by group
      · intro hv
        refine ⟨e.2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
        have := hv g hg
        calc g * (e : G) = (g * e * g⁻¹) * g := by group
          _ = (e : G) * g := by rw [this]
    rw [← hidx, ← hsub]
    rfl
  ·
    intro v hv hvℓ s hs hsv
    by_contra hsQ
    have ht := hsρ s hs
    have hw : Multiplicative.toAdd (ψ v) ≠ 0 := fun h0 => hvℓ (h0 ▸ ℓ.submodule.zero_mem)
    have hfixv : act (ρ s) ⟨v, hv⟩ = ⟨v, hv⟩ := Subtype.ext (by rw [hact]; exact hsv)
    have hmem := (hstab ⟨v, hv⟩ hw (ρ s)).mp hfixv
    have hne : Projectivization.mk k (Multiplicative.toAdd (ψ v)) hw ≠ ℓ := by
      intro heq
      apply hvℓ
      rw [← heq, Projectivization.submodule_mk]
      exact Submodule.mem_span_singleton_self _
    have hint : ρ s ∈ rootGrp (Projectivization.mk k (Multiplicative.toAdd (ψ v)) hw) ⊓ rootGrp ℓ :=
      ⟨hmem, ht⟩
    rw [rootGrp_inf_rootGrp hne, Subgroup.mem_bot] at hint
    exact hρne s hs hsQ hint

end IsNatBase

end Struct


end CFSG.QuasithinUnique.Setup.Campbell
