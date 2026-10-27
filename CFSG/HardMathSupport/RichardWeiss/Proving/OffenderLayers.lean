module

public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderGlue
public import CFSG.Quasithin.H13.A7Nat1238QZ

public section

namespace CFSG.HardMathSupport.RichardWeiss.Proving

open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry

variable {G : Type} [Group G]

@[expose] def layerFix (A X Y : Subgroup G) (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hYX : Y ≤ X) : Subgroup G where
  carrier := {x | x ∈ X ∧ ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ Y}
  one_mem' := ⟨X.one_mem, fun a _ => by simp [Y.one_mem]⟩
  mul_mem' := by
    rintro x x' ⟨hx, hxA⟩ ⟨hx', hx'A⟩
    refine ⟨X.mul_mem hx hx', fun a ha => ?_⟩
    have hc : x * (a * x' * a⁻¹ * x'⁻¹) = (a * x' * a⁻¹ * x'⁻¹) * x :=
      hX x hx _ (hYX (hx'A a ha))
    have hfac : a * (x * x') * a⁻¹ * (x * x')⁻¹ =
        (a * x * a⁻¹ * x⁻¹) * (x * (a * x' * a⁻¹ * x'⁻¹) * x⁻¹) := by group
    rw [hfac, hc]
    have hcancel : (a * x' * a⁻¹ * x'⁻¹) * x * x⁻¹ = a * x' * a⁻¹ * x'⁻¹ := by group
    rw [hcancel]
    exact Y.mul_mem (hxA a ha) (hx'A a ha)
  inv_mem' := by
    rintro x ⟨hx, hxA⟩
    refine ⟨X.inv_mem hx, fun a ha => ?_⟩
    have hcY : (a * x * a⁻¹ * x⁻¹)⁻¹ ∈ Y := Y.inv_mem (hxA a ha)
    have hc : x * (a * x * a⁻¹ * x⁻¹)⁻¹ = (a * x * a⁻¹ * x⁻¹)⁻¹ * x :=
      hX x hx _ (hYX hcY)
    have hfac : a * x⁻¹ * a⁻¹ * x⁻¹⁻¹ = x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x := by group
    have hcomm : x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x = (a * x * a⁻¹ * x⁻¹)⁻¹ := by
      calc x⁻¹ * (a * x * a⁻¹ * x⁻¹)⁻¹ * x
          = x⁻¹ * ((a * x * a⁻¹ * x⁻¹)⁻¹ * x) := mul_assoc _ _ _
        _ = x⁻¹ * (x * (a * x * a⁻¹ * x⁻¹)⁻¹) := by rw [hc]
        _ = (a * x * a⁻¹ * x⁻¹)⁻¹ := inv_mul_cancel_left _ _
    rw [hfac, hcomm]
    exact hcY

theorem mem_layerFix_iff (A X Y : Subgroup G) (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hYX : Y ≤ X) (x : G) :
    x ∈ layerFix A X Y hX hYX ↔ x ∈ X ∧ ∀ a ∈ A, a * x * a⁻¹ * x⁻¹ ∈ Y := Iff.rfl

theorem layerFix_le (A X Y : Subgroup G) (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a)
    (hYX : Y ≤ X) : layerFix A X Y hX hYX ≤ X :=
  fun _ hx => hx.1

theorem card_inf_centralizer_mul_le [Finite G] (A X Y : Subgroup G)
    (hX : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a) (hYX : Y ≤ X)
    (hAY : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) :
    Nat.card ↥(X ⊓ Subgroup.centralizer (A : Set G)) * Nat.card ↥Y ≤
      Nat.card ↥(Y ⊓ Subgroup.centralizer (A : Set G)) *
        Nat.card ↥(layerFix A X Y hX hYX) := by
  have hle : (X ⊓ Subgroup.centralizer (A : Set G)) ⊔ Y ≤ layerFix A X Y hX hYX := by
    refine sup_le ?_ ?_
    · intro x hx
      refine ⟨hx.1, fun a ha => ?_⟩
      have hcx : a * x = x * a := (Subgroup.mem_centralizer_iff.1 hx.2) a ha
      have h1 : a * x * a⁻¹ * x⁻¹ = 1 := by rw [hcx]; group
      rw [h1]
      exact Y.one_mem
    · intro y hy
      refine ⟨hYX hy, fun a ha => ?_⟩
      have h := Y.mul_mem (hAY a ha y hy) (Y.inv_mem hy)
      simpa [mul_assoc] using h
  have hcomm : ∀ x ∈ X ⊓ Subgroup.centralizer (A : Set G), ∀ y ∈ Y, x * y = y * x :=
    fun x hx y hy => hX x hx.1 y (hYX hy)
  have hprod := CFSG.Quasithin.H13.A7.card_sup_mul_card_inf_of_commute
    (X := X ⊓ Subgroup.centralizer (A : Set G)) (Y := Y) hcomm
  have hinf : (X ⊓ Subgroup.centralizer (A : Set G)) ⊓ Y = Y ⊓ Subgroup.centralizer (A : Set G) := by
    ext x
    constructor
    · rintro ⟨⟨_, hC⟩, hY⟩
      exact ⟨hY, hC⟩
    · rintro ⟨hY, hC⟩
      exact ⟨⟨hYX hY, hC⟩, hY⟩
  rw [hinf] at hprod
  have hle_card : Nat.card ↥((X ⊓ Subgroup.centralizer (A : Set G)) ⊔ Y) ≤
      Nat.card ↥(layerFix A X Y hX hYX) := Subgroup.card_le_of_le hle
  calc Nat.card ↥(X ⊓ Subgroup.centralizer (A : Set G)) * Nat.card ↥Y
      = Nat.card ↥((X ⊓ Subgroup.centralizer (A : Set G)) ⊔ Y) *
          Nat.card ↥(Y ⊓ Subgroup.centralizer (A : Set G)) := by rw [hprod, mul_comm]
    _ ≤ Nat.card ↥(layerFix A X Y hX hYX) * Nat.card ↥(Y ⊓ Subgroup.centralizer (A : Set G)) :=
        Nat.mul_le_mul_right _ hle_card
    _ = Nat.card ↥(Y ⊓ Subgroup.centralizer (A : Set G)) *
          Nat.card ↥(layerFix A X Y hX hYX) := mul_comm _ _

theorem relIndex_mul_card_of_le [Finite G] {H K : Subgroup G} (h : H ≤ K) :
    H.relIndex K * Nat.card ↥H = Nat.card ↥K := by
  have := Subgroup.relIndex_mul_card H K
  rwa [inf_of_le_left h] at this

theorem relIndex_layerFix_eq_altFix_index [Finite G] {U M A K : Subgroup G} {d : ℕ}
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hKU : K ≤ U) (hAM : A ≤ M)
    (hAU : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U)
    {π : ↥U →* Multiplicative (CFSG.RankThree.PartTwo.altHeart d)} (hπ : Function.Surjective π)
    (hπker : π.ker = K.subgroupOf U)
    {θ : ↥M →* Equiv.Perm (Fin d)} (hequiv : SectionEquiv U M π θ) :
    (layerFix A U K hUab hKU).relIndex U =
      (altFix d ((A.subgroupOf M).map θ)).index := by
  set E := (A.subgroupOf M).map θ with hE
  let Kf : Subgroup (Multiplicative (CFSG.RankThree.PartTwo.altHeart d)) :=
    AddSubgroup.toSubgroup (altFix d E)
  have hsub : (layerFix A U K hUab hKU).subgroupOf U = Kf.comap π := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    show (x : G) ∈ layerFix A U K hUab hKU ↔ Multiplicative.toAdd (π x) ∈ altFix d E
    rw [mem_layerFix_iff, mem_altFix_iff]
    constructor
    · rintro ⟨-, hxA⟩ g hg y hy
      obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.1 hg
      have hmA : (m : G) ∈ A := Subgroup.mem_subgroupOf.1 hm
      obtain ⟨u', hu'⟩ : ∃ u' : ↥U, (u' : G) = (m : G) * (x : G) * (m : G)⁻¹ :=
        ⟨⟨_, hAU (m : G) hmA x x.2⟩, rfl⟩
      have hk : u' * x⁻¹ ∈ K.subgroupOf U := by
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hu']
        exact hxA (m : G) hmA
      have hmod : π u' = π x := by
        have hker : u' * x⁻¹ ∈ π.ker := by rw [hπker]; exact hk
        have h1 := MonoidHom.mem_ker.1 hker
        calc π u' = π (u' * x⁻¹) * π x := by rw [← map_mul, inv_mul_cancel_right]
          _ = π x := by rw [h1, one_mul]
      have h2 := hequiv m x u' hu' y hy.symm
      rw [← h2, hmod]
    · intro hx
      refine ⟨x.2, fun a ha => ?_⟩
      obtain ⟨y, hy⟩ := QuotientAddGroup.mk_surjective (Multiplicative.toAdd (π x))
      have hθ : θ ⟨a, hAM ha⟩ ∈ E :=
        Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.2 ha)
      have h2 := hx _ hθ y hy
      obtain ⟨u', hu'⟩ : ∃ u' : ↥U, (u' : G) = a * (x : G) * a⁻¹ :=
        ⟨⟨_, hAU a ha x x.2⟩, rfl⟩
      have h3 := hequiv ⟨a, hAM ha⟩ x u' hu' y hy.symm
      have hπu' : π u' = π x := Multiplicative.toAdd.injective (h3.trans h2)
      have hmem : u' * x⁻¹ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπu', mul_inv_cancel]
      rw [hπker, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hu'] at hmem
      exact hmem
  rw [Subgroup.relIndex, hsub, Subgroup.index_comap_of_surjective Kf hπ, AddSubgroup.index_toSubgroup]

theorem relIndex_centralizer_mul_card (A X : Subgroup G) :
    (Subgroup.centralizer (A : Set G)).relIndex X *
        Nat.card ↥(X ⊓ Subgroup.centralizer (A : Set G)) = Nat.card ↥X := by
  rw [inf_comm]
  exact Subgroup.relIndex_mul_card _ _

theorem outer_nat_chain (a b c d cU cV cK fU fV nU nK nV : ℕ)
    (h1 : cV * nU ≤ cU * fV) (h2 : cU * nK ≤ cK * fU)
    (ha : a * cV = nV) (hb : b * fU = nU) (hc : c * fV = nV) (hd : d * cK = nK)
    (hcU : 0 < cU) (hcV : 0 < cV) (hcK : 0 < cK) (hfU : 0 < fU)
    (hnU : 0 < nU) (hnK : 0 < nK) (hnV : 0 < nV) (hab : a ≤ b) : d = 1 ∧ c = 1 := by
  have hkey : b * d * c ≤ a := by
    have hA : cU * (cV * nU * nK) ≤ cU * (fV * cK * fU) := by
      calc cU * (cV * nU * nK) = (cV * nU) * (cU * nK) := by ring
        _ ≤ (cU * fV) * (cK * fU) := Nat.mul_le_mul h1 h2
        _ = cU * (fV * cK * fU) := by ring
    have hB := Nat.le_of_mul_le_mul_left hA hcU
    rw [← hb, ← hd] at hB
    have hC : (cK * fU) * (cV * b * d) ≤ (cK * fU) * fV := by
      calc (cK * fU) * (cV * b * d) = cV * (b * fU) * (d * cK) := by ring
        _ ≤ fV * cK * fU := hB
        _ = (cK * fU) * fV := by ring
    have hD := Nat.le_of_mul_le_mul_left hC (Nat.mul_pos hcK hfU)
    have hE : cV * (b * d * c) ≤ cV * a := by
      calc cV * (b * d * c) = (cV * b * d) * c := by ring
        _ ≤ fV * c := Nat.mul_le_mul_right c hD
        _ = c * fV := by ring
        _ = nV := hc
        _ = a * cV := ha.symm
        _ = cV * a := by ring
    exact Nat.le_of_mul_le_mul_left hE hcV
  have hb0 : 0 < b := by
    rcases Nat.eq_zero_or_pos b with h | h
    · rw [h, zero_mul] at hb; omega
    · exact h
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, zero_mul] at hd; omega
    · exact h
  have hc0 : 0 < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h, zero_mul] at hc; omega
    · exact h
  have hdc : d * c ≤ 1 := by
    have h' : b * (d * c) ≤ b * 1 := by
      calc b * (d * c) = b * d * c := by ring
        _ ≤ a := hkey
        _ ≤ b := hab
        _ = b * 1 := (mul_one b).symm
    exact Nat.le_of_mul_le_mul_left h' hb0
  exact ⟨le_antisymm (by nlinarith) hd0, le_antisymm (by nlinarith) hc0⟩

theorem outer_layers_trivial_of_relIndex_le [Finite G]
    {V U K A M : Subgroup G} {d : ℕ}
    (hUV : U ≤ V) (hKU : K ≤ U) (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) (hAM : A ≤ M)
    (_hAV : ∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ ∈ V) (hAU : ∀ a ∈ A, ∀ u ∈ U, a * u * a⁻¹ ∈ U)
    {π : ↥U →* Multiplicative (CFSG.RankThree.PartTwo.altHeart d)} (hπ : Function.Surjective π)
    (hπker : π.ker = K.subgroupOf U)
    {θ : ↥M →* Equiv.Perm (Fin d)} (hequiv : SectionEquiv U M π θ)
    (heq : (Subgroup.centralizer (A : Set G)).relIndex V ≤
      (altFix d ((A.subgroupOf M).map θ)).index) :
    (∀ a ∈ A, ∀ k ∈ K, a * k = k * a) ∧ (∀ a ∈ A, ∀ v ∈ V, a * v * a⁻¹ * v⁻¹ ∈ U) := by
  have hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a :=
    fun a ha b hb => hV a (hUV ha) b (hUV hb)
  have h0 : ∀ σ : Equiv.Perm (Fin d), CFSG.RankThree.PartTwo.evenWeightPerm σ 0 = 0 :=
    fun σ => Subtype.ext rfl
  have hAK : ∀ a ∈ A, ∀ k ∈ K, a * k * a⁻¹ ∈ K := by
    intro a ha k hk
    have hkU : k ∈ U := hKU hk
    have hau : a * k * a⁻¹ ∈ U := hAU a ha k hkU
    have hk1 : π ⟨k, hkU⟩ = 1 := by
      have hmem : (⟨k, hkU⟩ : ↥U) ∈ π.ker := by
        rw [hπker, Subgroup.mem_subgroupOf]
        exact hk
      exact MonoidHom.mem_ker.1 hmem
    have h1 := hequiv ⟨a, hAM ha⟩ ⟨k, hkU⟩ ⟨a * k * a⁻¹, hau⟩ rfl 0
      (by rw [hk1, toAdd_one, QuotientAddGroup.mk_zero])
    have hpi : π ⟨a * k * a⁻¹, hau⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h1, h0, QuotientAddGroup.mk_zero, toAdd_one]
    have hmem : (⟨a * k * a⁻¹, hau⟩ : ↥U) ∈ π.ker := MonoidHom.mem_ker.2 hpi
    rw [hπker, Subgroup.mem_subgroupOf] at hmem
    exact hmem
  have hVU := card_inf_centralizer_mul_le A V U hV hUV hAU
  have hUK := card_inf_centralizer_mul_le A U K hUab hKU hAK
  have hcVmul := relIndex_centralizer_mul_card A V
  have hcKmul := relIndex_centralizer_mul_card A K
  have hbmul := relIndex_mul_card_of_le (layerFix_le A U K hUab hKU)
  have hcmul := relIndex_mul_card_of_le (layerFix_le A V U hV hUV)
  have hb := relIndex_layerFix_eq_altFix_index hUab hKU hAM hAU hπ hπker hequiv
  have hab : (Subgroup.centralizer (A : Set G)).relIndex V ≤
      (layerFix A U K hUab hKU).relIndex U := by
    rw [hb]
    exact heq
  obtain ⟨hd1, hc1⟩ := outer_nat_chain _ _ _ _ _ _ _ _ _ _ _ _
    hVU hUK hcVmul hbmul hcmul hcKmul
    (Nat.card_pos) (Nat.card_pos) (Nat.card_pos) (Nat.card_pos)
    (Nat.card_pos) (Nat.card_pos) (Nat.card_pos) hab
  constructor
  · intro a ha k hk
    have hKC : K ≤ Subgroup.centralizer (A : Set G) := Subgroup.relIndex_eq_one.1 hd1
    exact Subgroup.mem_centralizer_iff.1 (hKC hk) a ha
  · intro a ha v hv
    have hVF : V ≤ layerFix A V U hV hUV := Subgroup.relIndex_eq_one.1 hc1
    exact ((mem_layerFix_iff A V U hV hUV v).1 (hVF hv)).2 a ha

end CFSG.HardMathSupport.RichardWeiss.Proving
