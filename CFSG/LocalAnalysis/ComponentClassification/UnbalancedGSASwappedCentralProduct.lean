module

public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBPrimeJoinConvention
public import CFSG.LocalAnalysis.ComponentInitial.LocalComponents
public import CFSG.GroupTheory.PCore.PrimeCoreImages
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.ComponentClassification.UnbalancedGS

open Subgroup
open scoped commutatorElement Pointwise

namespace SwappedCentralProduct

theorem pow_two_pow_eq_one_of_mem_center {A : Type*} [Group A] [Finite A]
    (hcore : pPrimeCore 2 A = ⊥) {x : A} (hx : x ∈ center A) : ∃ k : ℕ, x ^ 2 ^ k = 1 := by
  obtain ⟨a, m, hm, hn⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos x).ne'
  refine ⟨a, ?_⟩
  have hy : orderOf (x ^ 2 ^ a) = m := by
    rw [orderOf_pow' x (by positivity), hn, Nat.gcd_mul_right_left,
      Nat.mul_div_cancel_left m (by positivity)]
  have hyc : x ^ 2 ^ a ∈ center A := pow_mem hx _
  have hnorm : (zpowers (x ^ 2 ^ a)).Normal := normal_of_le_center (zpowers_le.mpr hyc)
  have hcop : Nat.Coprime 2 (Nat.card (zpowers (x ^ 2 ^ a))) := by
    rw [Nat.card_zpowers, hy]
    exact Nat.coprime_two_left.mpr hm
  have hle : zpowers (x ^ 2 ^ a) ≤ pPrimeCore 2 A := le_sSup ⟨hnorm, hcop⟩
  rw [hcore, le_bot_iff] at hle
  have hmem : x ^ 2 ^ a ∈ zpowers (x ^ 2 ^ a) := mem_zpowers _
  rw [hle] at hmem
  exact mem_bot.mp hmem

theorem commutatorElement_central_mul_left {G : Type*} [Group G] {z : G}
    (hz : ∀ g, z * g = g * z) (x w : G) : ⁅z * x, w⁆ = ⁅x, w⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  calc z * x * w * (z * x)⁻¹ * w⁻¹ = z * (x * w * x⁻¹) * z⁻¹ * w⁻¹ := by group
    _ = x * w * x⁻¹ * z * z⁻¹ * w⁻¹ := by rw [hz]
    _ = x * w * x⁻¹ * w⁻¹ := by group

theorem commutatorElement_mul_central_right {G : Type*} [Group G] {z : G}
    (hz : ∀ g, z * g = g * z) (w y : G) : ⁅w, z * y⁆ = ⁅w, y⁆ := by
  rw [← commutatorElement_inv, commutatorElement_central_mul_left hz, commutatorElement_inv]

end SwappedCentralProduct

open SwappedCentralProduct

theorem swapped_central_product_fixed_layer {X : Type*} [Group X] [Finite X] (A B : Subgroup X)
    (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hA : IsQuasisimple A) (hcore : pPrimeCore 2 A = ⊥)
    (α : (A ⊔ B : Subgroup X) ≃* (A ⊔ B : Subgroup X)) (hα : ∀ k, α (α k) = k)
    (hαA : (A.subgroupOf (A ⊔ B)).map α.toMonoidHom = B.subgroupOf (A ⊔ B))
    (C : Subgroup (A ⊔ B : Subgroup X)) (hC : ∀ k, k ∈ C ↔ α k = k) :
    (∀ k : (A ⊔ B : Subgroup X), (k : X) ∈ A ⊓ B →
      ((α k : (A ⊔ B : Subgroup X)) : X) ∈ A ⊓ B) ∧
    (∀ d ∈ A ⊓ B, ∀ k ∈ A ⊔ B, d * k = k * d) ∧ IsPGroup 2 (A ⊓ B : Subgroup X) ∧
    ∃ δ : A →* (A ⊔ B : Subgroup X),
      (∀ u : A, δ u = Subgroup.inclusion le_sup_left u * α (Subgroup.inclusion le_sup_left u)) ∧
      (∀ u : A, δ u = 1 ↔ (u : X) ∈ B ∧
        α (Subgroup.inclusion le_sup_left u) = (Subgroup.inclusion le_sup_left u)⁻¹) ∧
      IsQuasisimple δ.range ∧
      C = δ.range ⊔ ((A ⊓ B).subgroupOf (A ⊔ B) ⊓ C) ∧
      pPrimeCore 2 C = ⊥ ∧ pPrimeCore 2 δ.range = ⊥ ∧
      ⁅C, C⁆ = δ.range ∧ (pLayer C 2).map C.subtype = δ.range ∧
      Nat.card (pLayer C 2) = Nat.card A / Nat.card δ.ker ∧
      Nat.card (pLayer C 2) ≤ Nat.card A ∧
      (Nat.card (pLayer C 2) = Nat.card A ↔ A ⊓ B = ⊥) ∧
      (A ⊓ B = ⊥ →
        (∃ e : A × B ≃* (A ⊔ B : Subgroup X), ∀ a b, (e (a, b) : X) = a * b) ∧
        C = δ.range ∧ Nonempty (A ≃* C)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ι : A →* (A ⊔ B : Subgroup X) := Subgroup.inclusion le_sup_left with hιdef
  have hι : ∀ u : A, ((ι u : (A ⊔ B : Subgroup X)) : X) = u := fun u => by
    rw [hιdef]
    rfl
  have hcommK : ∀ a b : (A ⊔ B : Subgroup X), (a : X) ∈ A → (b : X) ∈ B → a * b = b * a :=
    fun a b ha hb => Subtype.ext (hAB a ha b hb)
  have hαAB : ∀ k : (A ⊔ B : Subgroup X), (k : X) ∈ A → ((α k : _) : X) ∈ B := fun k hk => by
    have h : α k ∈ (A.subgroupOf (A ⊔ B)).map α.toMonoidHom := ⟨k, hk, rfl⟩
    rw [hαA] at h
    exact h
  have hαBA : ∀ k : (A ⊔ B : Subgroup X), (k : X) ∈ B → ((α k : _) : X) ∈ A := fun k hk => by
    have h : k ∈ (A.subgroupOf (A ⊔ B)).map α.toMonoidHom := by
      rw [hαA]
      exact hk
    obtain ⟨k', hk', rfl⟩ := h
    change ((α (α k') : (A ⊔ B : Subgroup X)) : X) ∈ A
    rw [hα]
    exact hk'
  have hDcent : ∀ d ∈ A ⊓ B, ∀ k ∈ A ⊔ B, d * k = k * d := by
    intro d hd k hk
    have hle : A ⊔ B ≤ centralizer ({d} : Set X) := by
      refine sup_le (fun a ha => ?_) (fun b hb => ?_) <;> rw [mem_centralizer_singleton_iff]
      · exact hAB a ha d (mem_inf.mp hd).2
      · exact (hAB d (mem_inf.mp hd).1 b hb).symm
    exact (mem_centralizer_singleton_iff.mp (hle hk)).symm
  have hDcentK : ∀ d : (A ⊔ B : Subgroup X), (d : X) ∈ A ⊓ B → ∀ k, d * k = k * d :=
    fun d hd k => Subtype.ext (hDcent d hd k k.2)
  have hDtwo : IsPGroup 2 (A ⊓ B : Subgroup X) := by
    intro d
    have hdA : (d : X) ∈ A := (mem_inf.mp d.2).1
    have hcen : (⟨d, hdA⟩ : A) ∈ center A := mem_center_iff.mpr fun g =>
      Subtype.ext (hDcent d d.2 g (le_sup_left (a := A) g.2)).symm
    obtain ⟨k, hk⟩ := pow_two_pow_eq_one_of_mem_center hcore hcen
    refine ⟨k, Subtype.ext ?_⟩
    have h := congrArg Subtype.val hk
    simpa using h
  have hDinv : ∀ k : (A ⊔ B : Subgroup X), (k : X) ∈ A ⊓ B →
      ((α k : (A ⊔ B : Subgroup X)) : X) ∈ A ⊓ B := fun k hk =>
    mem_inf.mpr ⟨hαBA k (mem_inf.mp hk).2, hαAB k (mem_inf.mp hk).1⟩
  refine ⟨hDinv, hDcent, hDtwo, ?_⟩
  let δ : A →* (A ⊔ B : Subgroup X) :=
    { toFun := fun u => ι u * α (ι u)
      map_one' := by simp
      map_mul' := fun u v => by
        have hc := hcommK (ι v) (α (ι u)) v.2 (hαAB _ u.2)
        change ι (u * v) * α (ι (u * v)) = ι u * α (ι u) * (ι v * α (ι v))
        rw [map_mul, map_mul]
        calc ι u * ι v * (α (ι u) * α (ι v)) = ι u * (ι v * α (ι u)) * α (ι v) := by group
          _ = ι u * (α (ι u) * ι v) * α (ι v) := by rw [hc]
          _ = ι u * α (ι u) * (ι v * α (ι v)) := by group }
  have hδ : ∀ u : A, δ u = ι u * α (ι u) := fun u => rfl
  have hδC : ∀ u : A, δ u ∈ C := fun u => by
    rw [hC, hδ, map_mul, hα]
    exact (hcommK (ι u) (α (ι u)) u.2 (hαAB _ u.2)).symm
  have hΔC : δ.range ≤ C := by
    rintro _ ⟨u, rfl⟩
    exact hδC u
  have hker : ∀ u : A, δ u = 1 ↔ (u : X) ∈ B ∧ α (ι u) = (ι u)⁻¹ := by
    intro u
    rw [hδ, mul_eq_one_iff_eq_inv']
    constructor
    · intro h
      refine ⟨?_, h⟩
      have h1 := hαAB (ι u) (by rw [hι]; exact u.2)
      rw [h] at h1
      have h2 := inv_mem h1
      rw [Subgroup.coe_inv, inv_inv, hι] at h2
      exact h2
    · exact fun h => h.2
  have hkerD : ∀ u ∈ δ.ker, (u : X) ∈ A ⊓ B := fun u hu => ⟨u.2, ((hker u).mp hu).1⟩
  have hnontriv : δ.range ≠ ⊥ := by
    intro hbot
    have hAB' : ∀ u : A, (u : X) ∈ B := fun u => ((hker u).mp (by
      have h : δ u ∈ δ.range := ⟨u, rfl⟩
      rw [hbot] at h
      exact h)).1
    obtain ⟨-, -, a, b, hab⟩ := hA
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
      (Subtype.ext (hAB a a.2 b (hAB' b)) : a * b = b * a)]
  have hΔ : IsQuasisimple δ.range :=
    (LocalAnalysis.ComponentInitial.quasisimple_homomorphic_images hA δ).resolve_left hnontriv
  have hkerCenter : δ.ker ≤ center A := fun u hu => mem_center_iff.mpr fun g =>
    Subtype.ext (hDcent u (hkerD u hu) g (le_sup_left (a := A) g.2)).symm
  have hker2 : IsPGroup 2 δ.ker := fun u => by
    obtain ⟨k, hk⟩ := hDtwo ⟨((u : A) : X), hkerD u u.2⟩
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    have h := congrArg Subtype.val hk
    simpa using h
  have hΔcore : pPrimeCore 2 δ.range = ⊥ := by
    rw [CFSG.central_p_kernel_prime_core_image δ.rangeRestrict δ.rangeRestrict_surjective
      (by rw [MonoidHom.ker_rangeRestrict]; exact hkerCenter)
      (by rw [MonoidHom.ker_rangeRestrict]; exact hker2), hcore, Subgroup.map_bot]
  have hBnorm : B ≤ normalizer (A : Set X) := fun b hb => by
    rw [mem_normalizer_iff]
    intro a
    constructor
    · intro ha
      rw [← hAB a ha b hb, mul_inv_cancel_right]
      exact ha
    · intro ha
      have h := hAB _ ha b⁻¹ (inv_mem hb)
      have hrw : a = b * a * b⁻¹ := by
        calc a = b⁻¹ * (b * a * b⁻¹) * b := by group
          _ = b * a * b⁻¹ * b⁻¹ * b := by rw [← h]
          _ = b * a * b⁻¹ := by group
      rw [hrw]
      exact ha
  have hsupset : ((A ⊔ B : Subgroup X) : Set X) = (A : Set X) * (B : Set X) :=
    coe_mul_of_right_le_normalizer_left A B hBnorm
  have hdec : ∀ k : (A ⊔ B : Subgroup X), ∃ u v : A, k = ι u * α (ι v) := by
    intro k
    have hk : (k : X) ∈ (A : Set X) * (B : Set X) := by
      rw [← hsupset]
      exact k.2
    obtain ⟨a, ha, b, hb, hab⟩ := hk
    let bK : (A ⊔ B : Subgroup X) := ⟨b, le_sup_right (a := A) hb⟩
    refine ⟨⟨a, ha⟩, ⟨α bK, hαBA bK hb⟩, Subtype.ext ?_⟩
    change (k : X) = a * ((α (α bK) : (A ⊔ B : Subgroup X)) : X)
    rw [hα]
    exact hab.symm
  have hCdec : ∀ k ∈ C, ∃ (z : (A ⊔ B : Subgroup X)) (v : A),
      (z : X) ∈ A ⊓ B ∧ α z = z ∧ k = z * δ v := by
    intro k hk
    obtain ⟨u, v, rfl⟩ := hdec k
    have hfix := (hC _).mp hk
    rw [map_mul, hα] at hfix
    have hcomm1 := hcommK (ι v) (α (ι u)) v.2 (hαAB _ u.2)
    have h : (ι v)⁻¹ * ι u = α (ι u) * (α (ι v))⁻¹ := by
      calc (ι v)⁻¹ * ι u = (ι v)⁻¹ * (ι u * α (ι v)) * (α (ι v))⁻¹ := by group
        _ = (ι v)⁻¹ * (α (ι u) * ι v) * (α (ι v))⁻¹ := by rw [← hfix]
        _ = (ι v)⁻¹ * (ι v * α (ι u)) * (α (ι v))⁻¹ := by rw [← hcomm1]
        _ = α (ι u) * (α (ι v))⁻¹ := by group
    have hd : ι (v⁻¹ * u) = α (ι (u * v⁻¹)) := by
      simp only [map_mul, map_inv]
      exact h
    have hdB : ((v⁻¹ * u : A) : X) ∈ B := by
      have h1 := hαAB (ι (u * v⁻¹)) (u * v⁻¹).2
      rw [← hd] at h1
      exact h1
    have hdD : ((ι (v⁻¹ * u) : (A ⊔ B : Subgroup X)) : X) ∈ A ⊓ B := ⟨(v⁻¹ * u).2, hdB⟩
    have hvd : v * (v⁻¹ * u) = (v⁻¹ * u) * v := Subtype.ext (hAB v v.2 _ hdB)
    have huv : u * v⁻¹ = v⁻¹ * u := by
      calc u * v⁻¹ = v * (v⁻¹ * u) * v⁻¹ := by group
        _ = v⁻¹ * u * v * v⁻¹ := by rw [hvd]
        _ = v⁻¹ * u := by group
    have hdfix : α (ι (v⁻¹ * u)) = ι (v⁻¹ * u) := by
      have h2 := hd
      rw [huv] at h2
      exact h2.symm
    refine ⟨ι (v⁻¹ * u), v, hdD, hdfix, ?_⟩
    have hu : ι u = ι v * ι (v⁻¹ * u) := by
      rw [← map_mul]
      congr 1
      group
    rw [hδ, hu, ← hDcentK _ hdD (ι v)]
    group
  have hCeq : C = δ.range ⊔ ((A ⊓ B).subgroupOf (A ⊔ B) ⊓ C) := by
    apply le_antisymm
    · intro k hk
      obtain ⟨z, v, hzD, hzα, rfl⟩ := hCdec k hk
      exact mul_mem (mem_sup_right ⟨hzD, (hC z).mpr hzα⟩) (mem_sup_left ⟨v, rfl⟩)
    · exact sup_le hΔC inf_le_right
  have hΔperf : ⁅δ.range, δ.range⁆ = δ.range := by
    have h := hΔ.1
    rw [Group.isPerfect_def, _root_.commutator_def] at h
    have h' := congrArg (Subgroup.map δ.range.subtype) h
    rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h'
  have hCC : ⁅C, C⁆ = δ.range := by
    apply le_antisymm
    · rw [Subgroup.commutator_le]
      intro g hg h hh
      obtain ⟨z₁, v₁, hz₁, -, rfl⟩ := hCdec g hg
      obtain ⟨z₂, v₂, hz₂, -, rfl⟩ := hCdec h hh
      rw [commutatorElement_central_mul_left (hDcentK z₁ hz₁),
        commutatorElement_mul_central_right (hDcentK z₂ hz₂)]
      exact ⟨⁅v₁, v₂⁆, map_commutatorElement δ v₁ v₂⟩
    · calc δ.range = ⁅δ.range, δ.range⁆ := hΔperf.symm
        _ ≤ ⁅C, C⁆ := Subgroup.commutator_mono hΔC hΔC
  set ΔC : Subgroup C := δ.range.subgroupOf C with hΔCdef
  have hΔCiso : ΔC ≃* δ.range := Subgroup.subgroupOfEquivOfLe hΔC
  have hΔCcore : pPrimeCore 2 ΔC = ⊥ := by
    have h := pPrimeCore_map_iso 2 hΔCiso
    rw [hΔcore] at h
    exact Subgroup.map_injective hΔCiso.injective (h.trans (Subgroup.map_bot _).symm)
  have hOC : pPrimeCore 2 C = ⊥ := by
    have hOcop : Nat.Coprime 2 (Nat.card (pPrimeCore 2 C)) :=
      pPrimeCore_coprime_card (p := 2) (G := C)
    have hOΔ : pPrimeCore 2 C ≤ ΔC := by
      intro o ho
      obtain ⟨z, v, hzD, -, hov⟩ := hCdec o o.2
      obtain ⟨k, hk⟩ := hDtwo ⟨z, hzD⟩
      have hzk : z ^ 2 ^ k = 1 := Subtype.ext (by
        have h := congrArg Subtype.val hk
        simpa using h)
      have hcop : Nat.Coprime (2 ^ k) (orderOf o) := by
        have h1 : orderOf (⟨o, ho⟩ : pPrimeCore 2 C) ∣ Nat.card (pPrimeCore 2 C) :=
          orderOf_dvd_natCard _
        rw [Subgroup.orderOf_mk] at h1
        exact Nat.Coprime.pow_left k (hOcop.coprime_dvd_right h1)
      obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
      have hpow : ((o ^ 2 ^ k : C) : (A ⊔ B : Subgroup X)) = (δ v) ^ 2 ^ k := by
        rw [SubgroupClass.coe_pow, hov, (Commute.mul_pow (hDcentK z hzD (δ v)) _), hzk,
          one_mul]
      change ((o : C) : (A ⊔ B : Subgroup X)) ∈ δ.range
      rw [← hm, SubgroupClass.coe_pow, hpow]
      exact pow_mem (pow_mem (⟨v, rfl⟩ : δ v ∈ δ.range) _) _
    have hO'n : ((pPrimeCore 2 C).subgroupOf ΔC).Normal :=
      (pPrimeCore_normal (p := 2) (G := C)).subgroupOf ΔC
    have hO'cop : Nat.Coprime 2 (Nat.card ((pPrimeCore 2 C).subgroupOf ΔC)) := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hOΔ).toEquiv]
      exact hOcop
    have hO'le : (pPrimeCore 2 C).subgroupOf ΔC ≤ pPrimeCore 2 ΔC := le_sSup ⟨hO'n, hO'cop⟩
    rw [hΔCcore, le_bot_iff] at hO'le
    rw [eq_bot_iff]
    intro o ho
    have h : (⟨o, hOΔ ho⟩ : ΔC) ∈ (pPrimeCore 2 C).subgroupOf ΔC := ho
    rw [hO'le] at h
    exact mem_bot.mpr (congrArg Subtype.val (mem_bot.mp h))
  have hΔCn : ΔC.Normal := by
    rw [hΔCdef, normal_subgroupOf_iff hΔC]
    intro x c hx hc
    obtain ⟨z, v, hzD, -, rfl⟩ := hCdec c hc
    have h1 : z * δ v * x * (z * δ v)⁻¹ = δ v * x * (δ v)⁻¹ := by
      calc z * δ v * x * (z * δ v)⁻¹ = z * (δ v * x * (δ v)⁻¹) * z⁻¹ := by group
        _ = δ v * x * (δ v)⁻¹ * z * z⁻¹ := by rw [hDcentK z hzD]
        _ = δ v * x * (δ v)⁻¹ := by group
    rw [h1]
    exact mul_mem (mul_mem ⟨v, rfl⟩ hx) (inv_mem ⟨v, rfl⟩)
  have hΔCq : IsQuasisimple ΔC := CFSG.LocalCores.isQuasisimple_of_mulEquiv hΔCiso.symm hΔ
  have hΔCcomp : IsPComponent 2 ΔC := by
    rw [CatalogueBPrimeJoin.pComponent_iff_subnormal_generated_quasisimple 2 ΔC]
    refine ⟨hΔCn.isSubnormal,
      CatalogueBPrimeJoin.primeResidual_eq_top_of_corefree_quasisimple 2 hΔCq hΔCcore, ?_⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hΔCcore).symm)
      hΔCq
  have hlayer : pLayer C 2 = ΔC := by
    apply le_antisymm
    · refine sSup_le fun L hL => ?_
      have hperf := CatalogueBHeldSmallCore.pComponent_perfect 2 L hL
      rw [Group.isPerfect_def, _root_.commutator_def] at hperf
      have hLL : ⁅L, L⁆ = L := by
        have h' := congrArg (Subgroup.map L.subtype) hperf
        rwa [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h'
      intro x hx
      rw [← hLL] at hx
      have hx' : (x : (A ⊔ B : Subgroup X)) ∈ ⁅C, C⁆ := by
        have h1 : ⁅L, L⁆.map C.subtype ≤ ⁅C, C⁆ := by
          rw [Subgroup.map_commutator]
          exact Subgroup.commutator_mono (map_subtype_le _) (map_subtype_le _)
        exact h1 ⟨x, hx, rfl⟩
      rw [hCC] at hx'
      exact hx'
    · exact le_sSup hΔCcomp
  have hlayermap : (pLayer C 2).map C.subtype = δ.range := by
    rw [hlayer, hΔCdef, Subgroup.subgroupOf_map_subtype, inf_of_le_left hΔC]
  have hcardΔ : Nat.card (pLayer C 2) = Nat.card δ.range := by
    rw [hlayer, Nat.card_congr hΔCiso.toEquiv]
  have hfirst : Nat.card A = Nat.card δ.range * Nat.card δ.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup δ.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange δ).toEquiv]
  have hkerbot : δ.ker = ⊥ ↔ A ⊓ B = ⊥ := by
    constructor
    · intro hk
      by_contra hD
      have hDnt : Nontrivial (A ⊓ B : Subgroup X) := (nontrivial_iff_ne_bot _).mpr hD
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hDtwo
      have hn0 : n ≠ 0 := by
        rintro rfl
        have h1 := Finite.one_lt_card (α := (A ⊓ B : Subgroup X))
        rw [hn, pow_zero] at h1
        exact lt_irrefl _ h1
      obtain ⟨d₀, hd₀⟩ := exists_prime_orderOf_dvd_card' (G := (A ⊓ B : Subgroup X)) 2
        (by rw [hn]; exact dvd_pow_self 2 hn0)
      have hd₀A : (d₀ : X) ∈ A := (mem_inf.mp d₀.2).1
      let dK : (A ⊔ B : Subgroup X) := ι ⟨d₀, hd₀A⟩
      have hdKD : (dK : X) ∈ A ⊓ B := d₀.2
      have hdK2 : dK * dK = 1 := by
        have h1 : d₀ ^ 2 = 1 := hd₀ ▸ pow_orderOf_eq_one d₀
        apply Subtype.ext
        have h2 := congrArg Subtype.val h1
        simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
        change (d₀ : X) * d₀ = 1
        rw [← sq]
        exact h2
      have hdK1 : dK ≠ 1 := by
        intro h
        have h0 : ((dK : (A ⊔ B : Subgroup X)) : X) = 1 := by rw [h]; rfl
        rw [hι] at h0
        have h1 : d₀ = 1 := Subtype.ext h0
        rw [h1, orderOf_one] at hd₀
        exact absurd hd₀ (by decide)
      have hmemker : ∀ e : (A ⊔ B : Subgroup X), (e : X) ∈ A ⊓ B → e ≠ 1 →
          α e = e⁻¹ → False := by
        intro e he he1 heα
        have hu : (⟨e, (mem_inf.mp he).1⟩ : A) ∈ δ.ker := by
          rw [MonoidHom.mem_ker, hker]
          exact ⟨(mem_inf.mp he).2, heα⟩
        rw [hk] at hu
        apply he1
        have h1 : (⟨e, (mem_inf.mp he).1⟩ : A) = 1 := mem_bot.mp hu
        exact Subtype.ext (show (e : X) = 1 from congrArg Subtype.val h1)
      by_cases hcase : α dK = dK⁻¹
      · exact hmemker dK hdKD hdK1 hcase
      ·
        set e := dK * α dK with he
        have hαdD := hDinv dK hdKD
        have heD : (e : X) ∈ A ⊓ B := mul_mem hdKD hαdD
        have hcomm : dK * α dK = α dK * dK := hDcentK dK hdKD (α dK)
        have he1 : e ≠ 1 := by
          intro h
          apply hcase
          rw [he] at h
          exact eq_inv_of_mul_eq_one_right h
        have heα : α e = e := by
          rw [he, map_mul, hα, ← hcomm]
        have he2 : e * e = 1 := by
          have hα2 : α dK * α dK = 1 := by rw [← map_mul, hdK2, map_one]
          calc e * e = dK * dK * (α dK * α dK) := by
                rw [he]
                calc dK * α dK * (dK * α dK) = dK * (α dK * dK) * α dK := by group
                  _ = dK * (dK * α dK) * α dK := by rw [hcomm]
                  _ = dK * dK * (α dK * α dK) := by group
            _ = 1 := by rw [hdK2, hα2, one_mul]
        exact hmemker e heD he1 (by rw [heα]; exact (inv_eq_of_mul_eq_one_right he2).symm)
    · intro hD
      rw [eq_bot_iff]
      intro u hu
      have h := hkerD u hu
      rw [hD, mem_bot] at h
      exact mem_bot.mpr (Subtype.ext h)
  have hpos : 0 < Nat.card δ.range := Nat.card_pos
  have hkerpos : 0 < Nat.card δ.ker := Nat.card_pos
  have hequal : A ⊓ B = ⊥ →
      (∃ e : A × B ≃* (A ⊔ B : Subgroup X), ∀ a b, (e (a, b) : X) = a * b) ∧
        C = δ.range ∧ Nonempty (A ≃* C) := by
    intro hD
    have hCΔ : C = δ.range := by
      rw [hCeq, hD, Subgroup.bot_subgroupOf, bot_inf_eq, sup_bot_eq]
    refine ⟨?_, hCΔ, ?_⟩
    · let μ : A × B →* (A ⊔ B : Subgroup X) :=
        MonoidHom.noncommCoprod (Subgroup.inclusion le_sup_left) (Subgroup.inclusion le_sup_right)
          fun a b => Subtype.ext (hAB a a.2 b b.2)
      have hμ : ∀ x : A × B, ((μ x : (A ⊔ B : Subgroup X)) : X) = x.1 * x.2 := fun _ => rfl
      have hinj : Function.Injective μ := by
        rw [injective_iff_map_eq_one]
        rintro ⟨a, b⟩ h
        have h' : (a : X) * b = 1 := by
          have h1 := congrArg Subtype.val h
          rwa [hμ] at h1
        have haB : (a : X) ∈ B := by
          rw [eq_inv_of_mul_eq_one_left h']
          exact inv_mem b.2
        have ha1 : (a : X) = 1 := by
          have h1 : (a : X) ∈ A ⊓ B := ⟨a.2, haB⟩
          rwa [hD, mem_bot] at h1
        have hb1 : (b : X) = 1 := by rw [ha1, one_mul] at h'; exact h'
        exact Prod.ext (Subtype.ext ha1) (Subtype.ext hb1)
      have hsurj : Function.Surjective μ := by
        intro k
        have hk : (k : X) ∈ (A : Set X) * (B : Set X) := by
          rw [← hsupset]
          exact k.2
        obtain ⟨a, ha, b, hb, hab⟩ := hk
        exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
      exact ⟨MulEquiv.ofBijective μ ⟨hinj, hsurj⟩, fun a b => rfl⟩
    · have hδinj : Function.Injective δ := by
        rw [← MonoidHom.ker_eq_bot_iff]
        exact hkerbot.mpr hD
      exact ⟨(MonoidHom.ofInjective hδinj).trans (MulEquiv.subgroupCongr hCΔ.symm)⟩
  refine ⟨δ, hδ, hker, hΔ, hCeq, hOC, hΔcore, hCC, hlayermap, ?_, ?_, ?_, hequal⟩
  · rw [hcardΔ, hfirst, Nat.mul_div_cancel _ hkerpos]
  · rw [hcardΔ, hfirst]
    exact Nat.le_mul_of_pos_right _ hkerpos
  · rw [← hkerbot, hcardΔ, hfirst]
    constructor
    · intro h
      have h1 : Nat.card δ.ker = 1 :=
        Nat.eq_of_mul_eq_mul_left hpos (h.symm.trans (mul_one _).symm)
      exact Subgroup.eq_bot_of_card_eq _ h1
    · intro h
      rw [h, Subgroup.card_bot, mul_one]

end CFSG.ComponentClassification.UnbalancedGS
